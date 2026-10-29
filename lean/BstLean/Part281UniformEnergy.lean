import BstLean.Part277Uniform
import BstLean.Part277Instances
import BstLean.Part253EnergyUpper

/-! Part 281, kappa cells: the 43 upper-energy certificates of Part264bUniformEnergy re-based to n0 = 11883
(valid for every n >= 11883), through Part277.energy_upper_from_kappasP. -/
namespace BstLean.Part281.UE
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206

theorem uniformEnergy10 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528005503957/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (56090099195879/80000000000000) := by
  have hk1 : kappa q ≤ 0.627899218111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528005503957 : ℝ)) (s := (0.849240948019 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629979029625 : ℝ) ≤ 0.699159928892 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629979029625 : ℝ)) (Q := (0.629979029625 : ℝ))
      (s := (0.776612144016 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.627899218111 : ℝ)) (U := (0.792666378294 : ℝ)) (R := (0.793249413218 : ℝ)) (Q2 := (0.629979029625 : ℝ)) (K2 := (0.699159928892 : ℝ)) (T := (0.836645346623 : ℝ))
    (B := ((56090099195879/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32925378397/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (700542205032277/1000000000000000) := by
  have hk1 : kappa q ≤ 0.627085955677 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526806054352 : ℝ)) (s := (0.849985518170 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629164218948 : ℝ) ≤ 0.698573290517 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629164218948 : ℝ)) (Q := (0.629164218948 : ℝ))
      (s := (0.777272401154 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.627085955677 : ℝ)) (U := (0.792153220560 : ℝ)) (R := (0.792736255484 : ℝ)) (Q2 := (0.629164218948 : ℝ)) (K2 := (0.698573290517 : ℝ)) (T := (0.836294274397 : ℝ))
    (B := ((700542205032277/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131401651187/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499794141803531/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626273251768 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525606604748 : ℝ)) (s := (0.850727745549 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628349967471 : ℝ) ≤ 0.697987342307 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628349967471 : ℝ)) (Q := (0.628349967471 : ℝ))
      (s := (0.777930792796 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.626273251768 : ℝ)) (U := (0.791640082951 : ℝ)) (R := (0.792223117875 : ℝ)) (Q2 := (0.628349967471 : ℝ)) (K2 := (0.697987342307 : ℝ)) (T := (0.835943468019 : ℝ))
    (B := ((3499794141803531/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524407155143/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496880544141191/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625461105711 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524407155143 : ℝ)) (s := (0.851467636282 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627536274520 : ℝ) ≤ 0.697402082941 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627536274520 : ℝ)) (Q := (0.627536274520 : ℝ))
      (s := (0.778587325971 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.625461105711 : ℝ)) (U := (0.791126965081 : ℝ)) (R := (0.791710000005 : ℝ)) (Q2 := (0.627536274520 : ℝ)) (K2 := (0.697402082941 : ℝ)) (T := (0.835592927032 : ℝ))
    (B := ((3496880544141191/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523207705539/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987940453337481/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624649516839 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523207705539 : ℝ)) (s := (0.852205196455 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626723139428 : ℝ) ≤ 0.696817511106 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626723139428 : ℝ)) (Q := (0.626723139428 : ℝ))
      (s := (0.779242007663 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.624649516839 : ℝ)) (U := (0.790613866566 : ℝ)) (R := (0.791196901490 : ℝ)) (Q2 := (0.626723139428 : ℝ)) (K2 := (0.696817511106 : ℝ)) (T := (0.835242650982 : ℝ))
    (B := ((6987940453337481/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (104401651187/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6982126367804951/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623838484488 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522008255935 : ℝ)) (s := (0.852940432115 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625910561526 : ℝ) ≤ 0.696233625487 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625910561526 : ℝ)) (Q := (0.625910561526 : ℝ))
      (s := (0.779894844816 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.623838484488 : ℝ)) (U := (0.790100787023 : ℝ)) (R := (0.790683821947 : ℝ)) (Q2 := (0.625910561526 : ℝ)) (K2 := (0.696233625487 : ℝ)) (T := (0.834892639416 : ℝ))
    (B := ((6982126367804951/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52080880633/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6976318820760949/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623028007996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520808806330 : ℝ)) (s := (0.853673349268 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625098540157 : ℝ) ≤ 0.695650424783 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625098540157 : ℝ)) (Q := (0.625098540157 : ℝ))
      (s := (0.780545844326 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.623028007996 : ℝ)) (U := (0.789587726072 : ℝ)) (R := (0.790170760996 : ℝ)) (Q2 := (0.625098540157 : ℝ)) (K2 := (0.695650424783 : ℝ)) (T := (0.834542891885 : ℝ))
    (B := ((6976318820760949/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259804678363/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6970517801324921/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622218086704 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519609356726 : ℝ)) (s := (0.854403953879 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624287074654 : ℝ) ≤ 0.695067907685 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624287074654 : ℝ)) (Q := (0.624287074654 : ℝ))
      (s := (0.781195013054 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.622218086704 : ℝ)) (U := (0.789074683329 : ℝ)) (R := (0.789657718253 : ℝ)) (Q2 := (0.624287074654 : ℝ)) (K2 := (0.695067907685 : ℝ)) (T := (0.834193407936 : ℝ))
    (B := ((6970517801324921/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518409907121/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1741180824664833/2500000000000000) := by
  have hk1 : kappa q ≤ 0.621408719956 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518409907121 : ℝ)) (s := (0.855132251877 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623476164364 : ℝ) ≤ 0.694486072897 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623476164364 : ℝ)) (Q := (0.623476164364 : ℝ))
      (s := (0.781842357813 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.621408719956 : ℝ)) (U := (0.788561658415 : ℝ)) (R := (0.789144693339 : ℝ)) (Q2 := (0.623476164364 : ℝ)) (K2 := (0.694486072897 : ℝ)) (T := (0.833844187123 : ℝ))
    (B := ((1741180824664833/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517210457517/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3479467650984699/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620599907103 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517210457517 : ℝ)) (s := (0.855858249149 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622665808638 : ℝ) ≤ 0.693904919126 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622665808638 : ℝ)) (Q := (0.622665808638 : ℝ))
      (s := (0.782487885372 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.620599907103 : ℝ)) (U := (0.788048650954 : ℝ)) (R := (0.788631685878 : ℝ)) (Q2 := (0.622665808638 : ℝ)) (K2 := (0.693904919126 : ℝ)) (T := (0.833495228999 : ℝ))
    (B := ((3479467650984699/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516011007913/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6953153800502817/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619791647492 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516011007913 : ℝ)) (s := (0.856581951545 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621856006817 : ℝ) ≤ 0.693324445077 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621856006817 : ℝ)) (Q := (0.621856006817 : ℝ))
      (s := (0.783131602469 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.619791647492 : ℝ)) (U := (0.787535660563 : ℝ)) (R := (0.788118695487 : ℝ)) (Q2 := (0.621856006817 : ℝ)) (K2 := (0.693324445077 : ℝ)) (T := (0.833146533116 : ℝ))
    (B := ((6953153800502817/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128702889577/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389475756709901/2000000000000000) := by
  have hk1 : kappa q ≤ 0.618983940480 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514811558308 : ℝ)) (s := (0.857303364879 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621046758260 : ℝ) ≤ 0.692744649467 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621046758260 : ℝ)) (Q := (0.621046758260 : ℝ))
      (s := (0.783773515791 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.618983940480 : ℝ)) (U := (0.787022686869 : ℝ)) (R := (0.787605721793 : ℝ)) (Q2 := (0.621046758260 : ℝ)) (K2 := (0.692744649467 : ℝ)) (T := (0.832798099034 : ℝ))
    (B := ((1389475756709901/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16050378397/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (867701280055167/1250000000000000) := by
  have hk1 : kappa q ≤ 0.618176785423 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513612108704 : ℝ)) (s := (0.858022494923 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620238062322 : ℝ) ≤ 0.692165531013 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620238062322 : ℝ)) (Q := (0.620238062322 : ℝ))
      (s := (0.784413631988 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.618176785423 : ℝ)) (U := (0.786509729495 : ℝ)) (R := (0.787092764419 : ℝ)) (Q2 := (0.620238062322 : ℝ)) (K2 := (0.692165531013 : ℝ)) (T := (0.832449926308 : ℝ))
    (B := ((867701280055167/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512412659099/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935848160551881/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617370181681 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512412659099 : ℝ)) (s := (0.858739347413 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619429918361 : ℝ) ≤ 0.691587088436 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619429918361 : ℝ)) (Q := (0.619429918361 : ℝ))
      (s := (0.785051957669 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.617370181681 : ℝ)) (U := (0.785996788065 : ℝ)) (R := (0.786579822989 : ℝ)) (Q2 := (0.619429918361 : ℝ)) (K2 := (0.691587088436 : ℝ)) (T := (0.832102014499 : ℝ))
    (B := ((6935848160551881/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102242641899/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6930092533296151/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616564128620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511213209495 : ℝ)) (s := (0.859453928049 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618622325740 : ℝ) ≤ 0.691009320463 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618622325740 : ℝ)) (Q := (0.618622325740 : ℝ))
      (s := (0.785688499405 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.616564128620 : ℝ)) (U := (0.785483862206 : ℝ)) (R := (0.786066897130 : ℝ)) (Q2 := (0.618622325740 : ℝ)) (K2 := (0.691009320463 : ℝ)) (T := (0.831754363166 : ℝ))
    (B := ((6930092533296151/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510013759891/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (346217167406517/500000000000000) := by
  have hk1 : kappa q ≤ 0.615758625605 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510013759891 : ℝ)) (s := (0.860166242492 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617815283828 : ℝ) ≤ 0.690432225827 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617815283828 : ℝ)) (Q := (0.617815283828 : ℝ))
      (s := (0.786323263721 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.615758625605 : ℝ)) (U := (0.784970951547 : ℝ)) (R := (0.785553986471 : ℝ)) (Q2 := (0.617815283828 : ℝ)) (K2 := (0.690432225827 : ℝ)) (T := (0.831406971874 : ℝ))
    (B := ((346217167406517/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (254407155143/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (276744023782063/400000000000000) := by
  have hk1 : kappa q ≤ 0.614953672004 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508814310286 : ℝ)) (s := (0.860876296368 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617008791987 : ℝ) ≤ 0.689855803257 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617008791987 : ℝ)) (Q := (0.617008791987 : ℝ))
      (s := (0.786956257114 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.614953672004 : ℝ)) (U := (0.784458055712 : ℝ)) (R := (0.785041090636 : ℝ)) (Q2 := (0.617008791987 : ℝ)) (K2 := (0.689855803257 : ℝ)) (T := (0.831059840183 : ℝ))
    (B := ((276744023782063/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253807430341/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912864262097661/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614149267194 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507614860682 : ℝ)) (s := (0.861584095266 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616202849594 : ℝ) ≤ 0.689280051496 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616202849594 : ℝ)) (Q := (0.616202849594 : ℝ))
      (s := (0.787587486031 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.614149267194 : ℝ)) (U := (0.783945174334 : ℝ)) (R := (0.784528209258 : ℝ)) (Q2 := (0.616202849594 : ℝ)) (K2 := (0.689280051496 : ℝ)) (T := (0.830712967662 : ℝ))
    (B := ((6912864262097661/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506415411077/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3453567170173419/5000000000000000) := by
  have hk1 : kappa q ≤ 0.613345410549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506415411077 : ℝ)) (s := (0.862289644739 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615397456021 : ℝ) ≤ 0.688704969286 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615397456021 : ℝ)) (Q := (0.615397456021 : ℝ))
      (s := (0.788216956887 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.613345410549 : ℝ)) (U := (0.783432307041 : ℝ)) (R := (0.784015341965 : ℝ)) (Q2 := (0.615397456021 : ℝ)) (K2 := (0.688704969286 : ℝ)) (T := (0.830366353876 : ℝ))
    (B := ((3453567170173419/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505215961473/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (690141081891753/1000000000000000) := by
  have hk1 : kappa q ≤ 0.612542101450 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505215961473 : ℝ)) (s := (0.862992950304 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614592610651 : ℝ) ≤ 0.688130555376 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614592610651 : ℝ)) (Q := (0.614592610651 : ℝ))
      (s := (0.788844676051 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.612542101450 : ℝ)) (U := (0.782919453467 : ℝ)) (R := (0.783502488391 : ℝ)) (Q2 := (0.614592610651 : ℝ)) (K2 := (0.688130555376 : ℝ)) (T := (0.830019998396 : ℝ))
    (B := ((690141081891753/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504016511869/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895693687468103/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611739339278 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504016511869 : ℝ)) (s := (0.863694017442 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613788312861 : ℝ) ≤ 0.687556808515 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613788312861 : ℝ)) (Q := (0.613788312861 : ℝ))
      (s := (0.789470649864 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.611739339278 : ℝ)) (U := (0.782406613242 : ℝ)) (R := (0.782989648166 : ℝ)) (Q2 := (0.613788312861 : ℝ)) (K2 := (0.687556808515 : ℝ)) (T := (0.829673900790 : ℝ))
    (B := ((6895693687468103/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62852132783/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444991467848311/5000000000000000) := by
  have hk1 : kappa q ≤ 0.610937123419 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502817062264 : ℝ)) (s := (0.864392851600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612984562037 : ℝ) ≤ 0.686983727461 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612984562037 : ℝ)) (Q := (0.612984562037 : ℝ))
      (s := (0.790094884622 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.610937123419 : ℝ)) (U := (0.781893786000 : ℝ)) (R := (0.782476820924 : ℝ)) (Q2 := (0.612984562037 : ℝ)) (K2 := (0.686983727461 : ℝ)) (T := (0.829328060632 : ℝ))
    (B := ((3444991467848311/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25080880633/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884278553340609/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610135453263 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501617612660 : ℝ)) (s := (0.865089458189 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612181357568 : ℝ) ≤ 0.686411310973 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612181357568 : ℝ)) (Q := (0.612181357568 : ℝ))
      (s := (0.790717386584 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.610135453263 : ℝ)) (U := (0.781380971377 : ℝ)) (R := (0.781964006301 : ℝ)) (Q2 := (0.612181357568 : ℝ)) (K2 := (0.686411310973 : ℝ)) (T := (0.828982477493 : ℝ))
    (B := ((6884278553340609/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100083632611/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (687858053017681/1000000000000000) := by
  have hk1 : kappa q ≤ 0.609334328201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500418163055 : ℝ)) (s := (0.865783842587 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611378698844 : ℝ) ≤ 0.685839557818 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611378698844 : ℝ)) (Q := (0.611378698844 : ℝ))
      (s := (0.791338161977 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.609334328201 : ℝ)) (U := (0.780868169007 : ℝ)) (R := (0.781451203931 : ℝ)) (Q2 := (0.611378698844 : ℝ)) (K2 := (0.685839557818 : ℝ)) (T := (0.828637150952 : ℝ))
    (B := ((687858053017681/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499218713451/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872888856020953/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608533747631 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499218713451 : ℝ)) (s := (0.866476010136 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610576585260 : ℝ) ≤ 0.685268466764 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610576585260 : ℝ)) (Q := (0.610576585260 : ℝ))
      (s := (0.791957216984 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.608533747631 : ℝ)) (U := (0.780355378528 : ℝ)) (R := (0.780938413452 : ℝ)) (Q2 := (0.610576585260 : ℝ)) (K2 := (0.685268466764 : ℝ)) (T := (0.828292080583 : ℝ))
    (B := ((6872888856020953/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498019263847/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6867203520727517/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607733710949 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498019263847 : ℝ)) (s := (0.867165966144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609775016213 : ℝ) ≤ 0.684698036583 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609775016213 : ℝ)) (Q := (0.609775016213 : ℝ))
      (s := (0.792574557757 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.607733710949 : ℝ)) (U := (0.779842599578 : ℝ)) (R := (0.780425634502 : ℝ)) (Q2 := (0.609775016213 : ℝ)) (K2 := (0.684698036583 : ℝ)) (T := (0.827947265966 : ℝ))
    (B := ((6867203520727517/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (248409907121/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430762257094751/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606934217557 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496819814242 : ℝ)) (s := (0.867853715886 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608973991103 : ℝ) ≤ 0.684128266053 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608973991103 : ℝ)) (Q := (0.608973991103 : ℝ))
      (s := (0.793190190409 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.606934217557 : ℝ)) (U := (0.779329831794 : ℝ)) (R := (0.779912866718 : ℝ)) (Q2 := (0.608973991103 : ℝ)) (K2 := (0.684128266053 : ℝ)) (T := (0.827602706680 : ℝ))
    (B := ((3430762257094751/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247810182319/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3427925913169097/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606135266861 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495620364638 : ℝ)) (s := (0.868539264603 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608173509335 : ℝ) ≤ 0.683559153958 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608173509335 : ℝ)) (Q := (0.608173509335 : ℝ))
      (s := (0.793804121017 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.606135266861 : ℝ)) (U := (0.778817074818 : ℝ)) (R := (0.779400109742 : ℝ)) (Q2 := (0.608173509335 : ℝ)) (K2 := (0.683559153958 : ℝ)) (T := (0.827258402309 : ℝ))
    (B := ((3427925913169097/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494420915033/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (342509272357147/500000000000000) := by
  have hk1 : kappa q ≤ 0.605336858268 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494420915033 : ℝ)) (s := (0.869222617503 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607373570315 : ℝ) ≤ 0.682990699082 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607373570315 : ℝ)) (Q := (0.607373570315 : ℝ))
      (s := (0.794416355624 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.605336858268 : ℝ)) (U := (0.778304328290 : ℝ)) (R := (0.778887363214 : ℝ)) (Q2 := (0.607373570315 : ℝ)) (K2 := (0.682990699082 : ℝ)) (T := (0.826914352436 : ℝ))
    (B := ((342509272357147/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493221465429/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422262683305461/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604538991190 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493221465429 : ℝ)) (s := (0.869903779760 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606574173453 : ℝ) ≤ 0.682422900216 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606574173453 : ℝ)) (Q := (0.606574173453 : ℝ))
      (s := (0.795026900237 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.604538991190 : ℝ)) (U := (0.777791591853 : ℝ)) (R := (0.778374626777 : ℝ)) (Q2 := (0.606574173453 : ℝ)) (K2 := (0.682422900216 : ℝ)) (T := (0.826570556645 : ℝ))
    (B := ((3422262683305461/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19680880633/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838871574786931/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603741665042 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492022015825 : ℝ)) (s := (0.870582756517 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605775318164 : ℝ) ≤ 0.681855756156 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605775318164 : ℝ)) (Q := (0.605775318164 : ℝ))
      (s := (0.795635760825 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.603741665042 : ℝ)) (U := (0.777278865150 : ℝ)) (R := (0.777861900074 : ℝ)) (Q2 := (0.605775318164 : ℝ)) (K2 := (0.681855756156 : ℝ)) (T := (0.826227014524 : ℝ))
    (B := ((6838871574786931/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24541128311/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416612030876573/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602944879240 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490822566220 : ℝ)) (s := (0.871259552883 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604977003863 : ℝ) ≤ 0.681289265702 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604977003863 : ℝ)) (Q := (0.604977003863 : ℝ))
      (s := (0.796242943327 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.602944879240 : ℝ)) (U := (0.776766147825 : ℝ)) (R := (0.777349182749 : ℝ)) (Q2 := (0.604977003863 : ℝ)) (K2 := (0.681289265702 : ℝ)) (T := (0.825883725663 : ℝ))
    (B := ((3416612030876573/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61202889577/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827582817628913/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602148633206 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489623116616 : ℝ)) (s := (0.871934173935 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604179229971 : ℝ) ≤ 0.680723427656 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604179229971 : ℝ)) (Q := (0.604179229971 : ℝ))
      (s := (0.796848453643 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.602148633206 : ℝ)) (U := (0.776253439524 : ℝ)) (R := (0.776836474448 : ℝ)) (Q2 := (0.604179229971 : ℝ)) (K2 := (0.680723427656 : ℝ)) (T := (0.825540689651 : ℝ))
    (B := ((6827582817628913/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488423667011/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (272877913302821/400000000000000) := by
  have hk1 : kappa q ≤ 0.601352926364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488423667011 : ℝ)) (s := (0.872606624720 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603381995910 : ℝ) ≤ 0.680158240827 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603381995910 : ℝ)) (Q := (0.603381995910 : ℝ))
      (s := (0.797452297641 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.601352926364 : ℝ)) (U := (0.775740739894 : ℝ)) (R := (0.776323774818 : ℝ)) (Q2 := (0.603381995910 : ℝ)) (K2 := (0.680158240827 : ℝ)) (T := (0.825197906082 : ℝ))
    (B := ((272877913302821/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487224217407/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (106504985887047/156250000000000) := by
  have hk1 : kappa q ≤ 0.600557758140 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487224217407 : ℝ)) (s := (0.873276910248 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602585301104 : ℝ) ≤ 0.679593704026 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602585301104 : ℝ)) (Q := (0.602585301104 : ℝ))
      (s := (0.798054481157 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.600557758140 : ℝ)) (U := (0.775228048581 : ℝ)) (R := (0.775811083505 : ℝ)) (Q2 := (0.602585301104 : ℝ)) (K2 := (0.679593704026 : ℝ)) (T := (0.824855374547 : ℝ))
    (B := ((106504985887047/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486024767803/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (53208567191093/78125000000000) := by
  have hk1 : kappa q ≤ 0.599763127966 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486024767803 : ℝ)) (s := (0.873945035504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601789144987 : ℝ) ≤ 0.679029816074 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601789144987 : ℝ)) (Q := (0.601789144987 : ℝ))
      (s := (0.798655009987 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.599763127966 : ℝ)) (U := (0.774715365236 : ℝ)) (R := (0.775298400160 : ℝ)) (Q2 := (0.601789144987 : ℝ)) (K2 := (0.679029816074 : ℝ)) (T := (0.824513094646 : ℝ))
    (B := ((53208567191093/78125000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (242412659099/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (425317520868941/625000000000000) := by
  have hk1 : kappa q ≤ 0.598969035274 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484825318198 : ℝ)) (s := (0.874611005439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600993526988 : ℝ) ≤ 0.678466575787 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600993526988 : ℝ)) (Q := (0.600993526988 : ℝ))
      (s := (0.799253889899 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.598969035274 : ℝ)) (U := (0.774202689508 : ℝ)) (R := (0.774785724432 : ℝ)) (Q2 := (0.600993526988 : ℝ)) (K2 := (0.678466575787 : ℝ)) (T := (0.824171065973 : ℝ))
    (B := ((425317520868941/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241812934297/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399735143701201/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598175479501 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483625868594 : ℝ)) (s := (0.875274824971 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600198446542 : ℝ) ≤ 0.677903981993 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600198446542 : ℝ)) (Q := (0.600198446542 : ℝ))
      (s := (0.799851126629 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.598175479501 : ℝ)) (U := (0.773690021047 : ℝ)) (R := (0.774273055971 : ℝ)) (Q2 := (0.600198446542 : ℝ)) (K2 := (0.677903981993 : ℝ)) (T := (0.823829288128 : ℝ))
    (B := ((3399735143701201/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482426418989/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793866451295759/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597382460087 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482426418989 : ℝ)) (s := (0.875936498990 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599403903091 : ℝ) ≤ 0.677342033523 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599403903091 : ℝ)) (Q := (0.599403903091 : ℝ))
      (s := (0.800446725873 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.597382460087 : ℝ)) (U := (0.773177359507 : ℝ)) (R := (0.773760394431 : ℝ)) (Q2 := (0.599403903091 : ℝ)) (K2 := (0.677342033523 : ℝ)) (T := (0.823487760714 : ℝ))
    (B := ((6793866451295759/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96245393877/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3394134407978309/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596589976474 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481226969385 : ℝ)) (s := (0.876596032353 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598609896071 : ℝ) ≤ 0.676780729208 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598609896071 : ℝ)) (Q := (0.598609896071 : ℝ))
      (s := (0.801040693303 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.596589976474 : ℝ)) (U := (0.772664704539 : ℝ)) (R := (0.773247739463 : ℝ)) (Q2 := (0.598609896071 : ℝ)) (K2 := (0.676780729208 : ℝ)) (T := (0.823146483330 : ℝ))
    (B := ((3394134407978309/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480027519781/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782676650540387/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595798028109 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480027519781 : ℝ)) (s := (0.877253429890 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597816424934 : ℝ) ≤ 0.676220067890 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597816424934 : ℝ)) (Q := (0.597816424934 : ℝ))
      (s := (0.801633034549 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.595798028109 : ℝ)) (U := (0.772152055800 : ℝ)) (R := (0.772735090724 : ℝ)) (Q2 := (0.597816424934 : ℝ)) (K2 := (0.676220067890 : ℝ)) (T := (0.822805455585 : ℝ))
    (B := ((6782676650540387/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (14963377193/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (677707587298503/1000000000000000) := by
  have hk1 : kappa q ≤ 0.595006614439 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478828070176 : ℝ)) (s := (0.877908696399 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597023489121 : ℝ) ≤ 0.675660048409 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597023489121 : ℝ)) (Q := (0.597023489121 : ℝ))
      (s := (0.802223755220 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.595006614439 : ℝ)) (U := (0.771639412942 : ℝ)) (R := (0.772222447866 : ℝ)) (Q2 := (0.597023489121 : ℝ)) (K2 := (0.675660048409 : ℝ)) (T := (0.822464677082 : ℝ))
    (B := ((677707587298503/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 11883 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (119407155143/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771478655718939/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594215734919 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477628620572 : ℝ)) (s := (0.878561836646 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596231088089 : ℝ) ≤ 0.675100669614 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596231088089 : ℝ)) (Q := (0.596231088089 : ℝ))
      (s := (0.802812860882 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 11883) (by norm_num) hn (q := q)
    (t := (3.464102 : ℝ)) (s0 := (0.9999999929 : ℝ)) (g0 := (0.99883425 : ℝ)) (G := (1.00116641 : ℝ)) (t2 := (3.466122 : ℝ))
    (r := (109009173 / 1000000 : ℝ)) (F := (8771 / 1000000 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (BstLean.Part277.finite_centre_11883 hn)
    (K1 := (0.594215734919 : ℝ)) (U := (0.771126775625 : ℝ)) (R := (0.771709810549 : ℝ)) (Q2 := (0.596231088089 : ℝ)) (K2 := (0.675100669614 : ℝ)) (T := (0.822124147430 : ℝ))
    (B := ((6771478655718939/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part281.UE

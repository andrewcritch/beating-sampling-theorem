import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S15
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12725 ≤ n) : wn n ≤ 1.035773718421 := by
  have hnR : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.805141726784 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.805141726784 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035773718421 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12725 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12725 + 24 / (12725 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12725 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008473053168 : ℝ) := by
  have hnR : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.805141726784 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hnrpos : 0 < √(n : ℝ) := sqrt_pos.mpr hnpos
  have ha := alphaJ_le (by omega : 1000 ≤ n)
  have hb := betaJ_le (by omega : 4096 ≤ n)
  have ha0 := alphaJ_nonneg n
  have hb0 := betaJ_nonneg n
  have hw := wn_upper hn
  have hw0 : 0 ≤ wn n := by unfold wn; positivity
  have hc := BstLean.Part253.cs_lower
  have hdc := deltaChi_upper hn
  have hdc0 : 0 ≤ deltaChi n 12 := by unfold deltaChi; positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hbmax : betaJ n ≤ 81 / 1000 / (12725 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035773718421 * (81 / 1000 / 12725)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035773718421 * n *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot3 : √((n : ℝ) / csC) ≤ 0.878679 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (n : ℝ) / 1.29521 := div_le_div_of_nonneg_left hn0 (by norm_num) hc
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  calc
    _ ≤ (1792 / 10000 / (n : ℝ)) * (1.421981 * √(n : ℝ)) +
        2 * (1792 / 10000 / n) * (1.62763 * √(n : ℝ)) +
        4 * (1 / 2.506628) * 1.035773718421 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035773718421 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035773718421 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12725)) / 112.805141726784 := by gcongr
    _ ≤ (0.008473053168 : ℝ) := by norm_num

end BstLean.Part269.S15
namespace BstLean.Part269.S15
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12725 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12725 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12725 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12725 + 0.008473053168 / 112.805141726784) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12725 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12725 := by gcongr
    linarith
  have hm0 : 0 ≤ meanRoot n q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := BstLean.Part264.gMinus_lower (by omega : 12225 ≤ n)
  have hg0 : 0 < gMinus n := by linarith
  have hratio : energyRatio n (gMinus n) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio n (gMinus n) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio n (gMinus n) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio n (gMinus n) q)
    (by linarith : energyRatio n (gMinus n) q ≤ 1)).1
  have hgp := BstLean.Part264.gPlus_upper (by omega : 12225 ≤ n)
  have hgp0 : 0 ≤ BstLean.Part211.gPlus n := le_trans zero_le_one (BstLean.Part264.gPlus_lower n)
  have ht : √(BstLean.Part211.gPlus n * kappa (energyRatio n (gMinus n) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus n) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (112.805141726784 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S15.finite_centre_upper (by omega : 12725 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264031592993/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010172857128923/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627938342326 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528063185986 : ℝ)) (s := (0.849205082184 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629908498741 : ℝ) ≤ 0.699109137460 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629908498741 : ℝ)) (Q := (0.629908498741 : ℝ))
      (s := (0.776669352566 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792673494975 : ℝ)) (R := (0.793217951086 : ℝ)) (Q2 := (0.629908498741 : ℝ)) (T := (0.836601322865 : ℝ))
    (B := ((7010172857128923/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105373900917/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502180719125743/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627128962821 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526869504585 : ℝ)) (s := (0.849946189555 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629097644306 : ℝ) ≤ 0.698525371566 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629097644306 : ℝ)) (Q := (0.629097644306 : ℝ))
      (s := (0.777326285371 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792162792695 : ℝ)) (R := (0.792707248806 : ℝ)) (Q2 := (0.629097644306 : ℝ)) (T := (0.836251963025 : ℝ))
    (B := ((3502180719125743/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32854738949/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998556537801763/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626320136517 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525675823184 : ℝ)) (s := (0.850684976311 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628287343721 : ℝ) ≤ 0.697942289166 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628287343721 : ℝ)) (Q := (0.628287343721 : ℝ))
      (s := (0.777981371063 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791652110353 : ℝ)) (R := (0.792196566464 : ℝ)) (Q2 := (0.628287343721 : ℝ)) (T := (0.835902866472 : ℝ))
    (B := ((6998556537801763/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262241070891/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496379072442159/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625511862750 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524482141782 : ℝ)) (s := (0.851421448492 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477596323 : ℝ) ≤ 0.697359888956 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477596323 : ℝ)) (Q := (0.627477596323 : ℝ))
      (s := (0.778634616565 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791141447568 : ℝ)) (R := (0.791685903679 : ℝ)) (Q2 := (0.627477596323 : ℝ)) (T := (0.835554032754 : ℝ))
    (B := ((3496379072442159/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523288460381/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (698696624864699/1000000000000000) := by
  have hk1 : kappa q ≤ 0.624704140864 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523288460381 : ℝ)) (s := (0.852155612100 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668401451 : ℝ) ≤ 0.696778169642 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668401451 : ℝ)) (Q := (0.626668401451 : ℝ))
      (s := (0.779286028762 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790630803962 : ℝ)) (R := (0.791175260073 : ℝ)) (Q2 := (0.626668401451 : ℝ)) (T := (0.835205461426 : ℝ))
    (B := ((698696624864699/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522094778979/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981180838280617/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623896970202 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522094778979 : ℝ)) (s := (0.852887473096 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859758449 : ℝ) ≤ 0.696197129930 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859758449 : ℝ)) (Q := (0.625859758449 : ℝ))
      (s := (0.779935614493 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790120179157 : ℝ)) (R := (0.790664635268 : ℝ)) (Q2 := (0.625859758449 : ℝ)) (T := (0.834857152040 : ℝ))
    (B := ((6981180838280617/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (260450548789/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1743850475754693/2500000000000000) := by
  have hk1 : kappa q ≤ 0.623090350113 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520901097578 : ℝ)) (s := (0.853617037402 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625051666666 : ℝ) ≤ 0.695616768533 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625051666666 : ℝ)) (Q := (0.625051666666 : ℝ))
      (s := (0.780583380555 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789609572778 : ℝ)) (R := (0.790154028889 : ℝ)) (Q2 := (0.625051666666 : ℝ)) (T := (0.834509104153 : ℝ))
    (B := ((1743850475754693/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519707416177/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (435601839508593/625000000000000) := by
  have hk1 : kappa q ≤ 0.622284279948 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519707416177 : ℝ)) (s := (0.854344310903 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624244125449 : ℝ) ≤ 0.695037084166 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624244125449 : ℝ)) (Q := (0.624244125449 : ℝ))
      (s := (0.781229333706 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789098984448 : ℝ)) (R := (0.789643440559 : ℝ)) (Q2 := (0.624244125449 : ℝ)) (T := (0.834161317319 : ℝ))
    (B := ((435601839508593/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20740549391/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6963863414954999/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621478759059 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518513734775 : ℝ)) (s := (0.855069299443 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623437134152 : ℝ) ≤ 0.694458075550 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623437134152 : ℝ)) (Q := (0.623437134152 : ℝ))
      (s := (0.781873480661 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788588413793 : ℝ)) (R := (0.789132869904 : ℝ)) (Q2 := (0.623437134152 : ℝ)) (T := (0.833813791100 : ℝ))
    (B := ((6963863414954999/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258660026687/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (278324153633259/400000000000000) := by
  have hk1 : kappa q ≤ 0.620673786805 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517320053374 : ℝ)) (s := (0.855792008830 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622630692130 : ℝ) ≤ 0.693879741407 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622630692130 : ℝ)) (Q := (0.622630692130 : ℝ))
      (s := (0.782515828095 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788077860439 : ℝ)) (R := (0.788622316550 : ℝ)) (Q2 := (0.622630692130 : ℝ)) (T := (0.833466525051 : ℝ))
    (B := ((278324153633259/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129031592993/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (173808767479219/250000000000000) := by
  have hk1 : kappa q ≤ 0.619869362544 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516126371972 : ℝ)) (s := (0.856512444834 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621824798741 : ℝ) ≤ 0.693302080463 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621824798741 : ℝ)) (Q := (0.621824798741 : ℝ))
      (s := (0.783156382641 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787567324013 : ℝ)) (R := (0.788111780124 : ℝ)) (Q2 := (0.621824798741 : ℝ)) (T := (0.833119518735 : ℝ))
    (B := ((173808767479219/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514932690571/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6946603979410119/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619065485641 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514932690571 : ℝ)) (s := (0.857230613185 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621019453351 : ℝ) ≤ 0.692725091456 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621019453351 : ℝ)) (Q := (0.621019453351 : ℝ))
      (s := (0.783795150891 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787056804145 : ℝ)) (R := (0.787601260256 : ℝ)) (Q2 := (0.621019453351 : ℝ)) (T := (0.832772771716 : ℝ))
    (B := ((6946603979410119/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51373900917/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (867607958879997/1250000000000000) := by
  have hk1 : kappa q ≤ 0.618262155462 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513739009170 : ℝ)) (s := (0.857946519579 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620214655320 : ℝ) ≤ 0.692148773116 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620214655320 : ℝ)) (Q := (0.620214655320 : ℝ))
      (s := (0.784432139402 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786546300462 : ℝ)) (R := (0.787090756573 : ℝ)) (Q2 := (0.620214655320 : ℝ)) (T := (0.832426283555 : ℝ))
    (B := ((867607958879997/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64068165971/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1387025952716733/2000000000000000) := by
  have hk1 : kappa q ≤ 0.617459371375 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512545327768 : ℝ)) (s := (0.858660169674 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619410404019 : ℝ) ≤ 0.691573124185 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619410404019 : ℝ)) (Q := (0.619410404019 : ℝ))
      (s := (0.785067354686 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786035812596 : ℝ)) (R := (0.786580268707 : ℝ)) (Q2 := (0.619410404019 : ℝ)) (T := (0.832080053818 : ℝ))
    (B := ((1387025952716733/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511351646367/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (866175280825897/1250000000000000) := by
  have hk1 : kappa q ≤ 0.616657132753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511351646367 : ℝ)) (s := (0.859371569089 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618606698819 : ℝ) ≤ 0.690998143409 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618606698819 : ℝ)) (Q := (0.618606698819 : ℝ))
      (s := (0.785700803218 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785525340178 : ℝ)) (R := (0.786069796289 : ℝ)) (Q2 := (0.618606698819 : ℝ)) (T := (0.831734082075 : ℝ))
    (B := ((866175280825897/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102031592993/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1730920277429227/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615855438972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510157964965 : ℝ)) (s := (0.860080723411 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617803539096 : ℝ) ≤ 0.690423829536 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617803539096 : ℝ)) (Q := (0.617803539096 : ℝ))
      (s := (0.786332491432 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785014882841 : ℝ)) (R := (0.785559338952 : ℝ)) (Q2 := (0.617803539096 : ℝ)) (T := (0.831388367892 : ℝ))
    (B := ((1730920277429227/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127241070891/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3458983171279709/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615054289411 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508964283564 : ℝ)) (s := (0.860787638188 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617000924224 : ℝ) ≤ 0.689850181316 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617000924224 : ℝ)) (Q := (0.617000924224 : ℝ))
      (s := (0.786962425728 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784504440217 : ℝ)) (R := (0.785048896328 : ℝ)) (Q2 := (0.617000924224 : ℝ)) (T := (0.831042910839 : ℝ))
    (B := ((3458983171279709/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507770602163/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912257934821181/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614253683451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507770602163 : ℝ)) (s := (0.861492318933 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616198853586 : ℝ) ≤ 0.689277197507 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616198853586 : ℝ)) (Q := (0.616198853586 : ℝ))
      (s := (0.787590612463 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783994011942 : ℝ)) (R := (0.784538468053 : ℝ)) (Q2 := (0.616198853586 : ℝ)) (T := (0.830697710487 : ℝ))
    (B := ((6912257934821181/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506576920761/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906555876228343/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613453620476 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506576920761 : ℝ)) (s := (0.862194771124 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615397326564 : ℝ) ≤ 0.688704876871 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615397326564 : ℝ)) (Q := (0.615397326564 : ℝ))
      (s := (0.788217057960 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783483597649 : ℝ)) (R := (0.784028053760 : ℝ)) (Q2 := (0.615397326564 : ℝ)) (T := (0.830352766411 : ℝ))
    (B := ((6906555876228343/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1579322623/3125000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1380172031309297/2000000000000000) := by
  have hk1 : kappa q ≤ 0.612654099875 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505383239360 : ℝ)) (s := (0.862895000203 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614596342547 : ℝ) ≤ 0.688133218172 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614596342547 : ℝ)) (Q := (0.614596342547 : ℝ))
      (s := (0.788841768499 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782973196977 : ℝ)) (R := (0.783517653088 : ℝ)) (Q2 := (0.614596342547 : ℝ)) (T := (0.830008078185 : ℝ))
    (B := ((1380172031309297/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252094778979/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (344758538279019/500000000000000) := by
  have hk1 : kappa q ≤ 0.611855121039 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504189557958 : ℝ)) (s := (0.863593011578 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613795900922 : ℝ) ≤ 0.687562220178 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613795900922 : ℝ)) (Q := (0.613795900922 : ℝ))
      (s := (0.789464750329 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782462809562 : ℝ)) (R := (0.783007265673 : ℝ)) (Q2 := (0.613795900922 : ℝ)) (T := (0.829663645385 : ℝ))
    (B := ((344758538279019/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502995876557/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1722371923293439/2500000000000000) := by
  have hk1 : kappa q ≤ 0.611056683363 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502995876557 : ℝ)) (s := (0.864288810623 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612996001088 : ℝ) ≤ 0.686991881668 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612996001088 : ℝ)) (Q := (0.612996001088 : ℝ))
      (s := (0.790086009654 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781952435045 : ℝ)) (R := (0.782496891156 : ℝ)) (Q2 := (0.612996001088 : ℝ)) (T := (0.829319467590 : ℝ))
    (B := ((1722371923293439/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100360439031/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1376762185841813/2000000000000000) := by
  have hk1 : kappa q ≤ 0.610258786243 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501802195155 : ℝ)) (s := (0.864982402676 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612196642435 : ℝ) ≤ 0.686422201413 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612196642435 : ℝ)) (Q := (0.612196642435 : ℝ))
      (s := (0.790705552650 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781442073063 : ℝ)) (R := (0.781986529174 : ℝ)) (Q2 := (0.612196642435 : ℝ)) (T := (0.828975544378 : ℝ))
    (B := ((1376762185841813/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250304256877/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27512561854429/40000000000000) := by
  have hk1 : kappa q ≤ 0.609461429080 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500608513754 : ℝ)) (s := (0.865673793041 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611397824365 : ℝ) ≤ 0.685853178200 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611397824365 : ℝ)) (Q := (0.611397824365 : ℝ))
      (s := (0.791323385452 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780931723257 : ℝ)) (R := (0.781476179368 : ℝ)) (Q2 := (0.611397824365 : ℝ)) (T := (0.828631875333 : ℝ))
    (B := ((27512561854429/40000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499414832353/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (859059535790939/1250000000000000) := by
  have hk1 : kappa q ≤ 0.608664611278 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499414832353 : ℝ)) (s := (0.866362986990 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610599546280 : ℝ) ≤ 0.685284810811 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610599546280 : ℝ)) (Q := (0.610599546280 : ℝ))
      (s := (0.791939514157 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780421385270 : ℝ)) (R := (0.780965841381 : ℝ)) (Q2 := (0.610599546280 : ℝ)) (T := (0.828288460033 : ℝ))
    (B := ((859059535790939/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498221150951/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866818387367081/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607868332243 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498221150951 : ℝ)) (s := (0.867049989762 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609801807588 : ℝ) ≤ 0.684717098041 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609801807588 : ℝ)) (Q := (0.609801807588 : ℝ))
      (s := (0.792553944828 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779911058745 : ℝ)) (R := (0.780455514856 : ℝ)) (Q2 := (0.609801807588 : ℝ)) (T := (0.827945298068 : ℝ))
    (B := ((6866818387367081/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (9940549391/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430583378380497/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607072591386 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497027469550 : ℝ)) (s := (0.867734806559 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609004607695 : ℝ) ≤ 0.684150038682 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609004607695 : ℝ)) (Q := (0.609004607695 : ℝ))
      (s := (0.793166683495 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779400743325 : ℝ)) (R := (0.779945199436 : ℝ)) (Q2 := (0.609004607695 : ℝ)) (T := (0.827602389021 : ℝ))
    (B := ((3430583378380497/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123958447037/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855521384581863/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606277388118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495833788148 : ℝ)) (s := (0.868417442554 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608207946012 : ℝ) ≤ 0.683583631533 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608207946012 : ℝ)) (Q := (0.608207946012 : ℝ))
      (s := (0.793777736151 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778890438654 : ℝ)) (R := (0.779434894765 : ℝ)) (Q2 := (0.608207946012 : ℝ)) (T := (0.827259732480 : ℝ))
    (B := ((6855521384581863/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494640106747/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849882260939659/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605482721857 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494640106747 : ℝ)) (s := (0.869097902884 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607411821958 : ℝ) ≤ 0.683017875398 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607411821958 : ℝ)) (Q := (0.607411821958 : ℝ))
      (s := (0.794387108749 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778380144381 : ℝ)) (R := (0.778924600492 : ℝ)) (Q2 := (0.607411821958 : ℝ)) (T := (0.826917328036 : ℝ))
    (B := ((6849882260939659/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246723212673/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (427765585998843/625000000000000) := by
  have hk1 : kappa q ≤ 0.604688592022 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493446425346 : ℝ)) (s := (0.869776192658 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606616234949 : ℝ) ≤ 0.682452769085 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606616234949 : ℝ)) (Q := (0.606616234949 : ℝ))
      (s := (0.794994807214 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777869860151 : ℝ)) (R := (0.778414316262 : ℝ)) (Q2 := (0.606616234949 : ℝ)) (T := (0.826575175278 : ℝ))
    (B := ((427765585998843/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61531592993/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683862271989137/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603894998033 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492252743944 : ℝ)) (s := (0.870452316948 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605821184405 : ℝ) ≤ 0.681888311404 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605821184405 : ℝ)) (Q := (0.605821184405 : ℝ))
      (s := (0.795600837435 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777359585612 : ℝ)) (R := (0.777904041723 : ℝ)) (Q2 := (0.605821184405 : ℝ)) (T := (0.826233273800 : ℝ))
    (B := ((683862271989137/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491059062543/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (273320091315601/400000000000000) := by
  have hk1 : kappa q ≤ 0.603101939318 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491059062543 : ℝ)) (s := (0.871126280797 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605026669751 : ℝ) ≤ 0.681324501172 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605026669751 : ℝ)) (Q := (0.605026669751 : ℝ))
      (s := (0.796205205265 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776849320414 : ℝ)) (R := (0.777393776525 : ℝ)) (Q2 := (0.605026669751 : ℝ)) (T := (0.825891623196 : ℝ))
    (B := ((273320091315601/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489865381141/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (213355876726083/312500000000000) := by
  have hk1 : kappa q ≤ 0.602309415304 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489865381141 : ℝ)) (s := (0.871798089216 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604232690415 : ℝ) ≤ 0.680761337210 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604232690415 : ℝ)) (Q := (0.604232690415 : ℝ))
      (s := (0.796807916524 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776339064207 : ℝ)) (R := (0.776883520318 : ℝ)) (Q2 := (0.604232690415 : ℝ)) (T := (0.825550223063 : ℝ))
    (B := ((213355876726083/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24433584987/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821780027218733/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601517425424 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488671699740 : ℝ)) (s := (0.872467747183 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603439245829 : ℝ) ≤ 0.680198818342 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603439245829 : ℝ)) (Q := (0.603439245829 : ℝ))
      (s := (0.797408976996 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775828816643 : ℝ)) (R := (0.776373272754 : ℝ)) (Q2 := (0.603439245829 : ℝ)) (T := (0.825209072999 : ℝ))
    (B := ((6821780027218733/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487478018339/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1704044547292947/2500000000000000) := by
  have hk1 : kappa q ≤ 0.600725969111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487478018339 : ℝ)) (s := (0.873135259646 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602646335422 : ℝ) ≤ 0.679636943396 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602646335422 : ℝ)) (Q := (0.602646335422 : ℝ))
      (s := (0.798008392439 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775318577373 : ℝ)) (R := (0.775863033484 : ℝ)) (Q2 := (0.602646335422 : ℝ)) (T := (0.824868172601 : ℝ))
    (B := ((1704044547292947/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486284336937/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1362116506291839/2000000000000000) := by
  have hk1 : kappa q ≤ 0.599935045804 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486284336937 : ℝ)) (s := (0.873800631523 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601853958637 : ℝ) ≤ 0.679075711207 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601853958637 : ℝ)) (Q := (0.601853958637 : ℝ))
      (s := (0.798606168567 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774808346053 : ℝ)) (R := (0.775352802164 : ℝ)) (Q2 := (0.601853958637 : ℝ)) (T := (0.824527521474 : ℝ))
    (B := ((1362116506291839/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30318165971/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (680499304448197/1000000000000000) := by
  have hk1 : kappa q ≤ 0.599144654943 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485090655536 : ℝ)) (s := (0.874463867700 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601062114909 : ℝ) ≤ 0.678515120610 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601062114909 : ℝ)) (Q := (0.601062114909 : ℝ))
      (s := (0.799202311071 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774298122335 : ℝ)) (R := (0.774842578446 : ℝ)) (Q2 := (0.601062114909 : ℝ)) (T := (0.824187119218 : ℝ))
    (B := ((680499304448197/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241948487067/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (84992621483457/125000000000000) := by
  have hk1 : kappa q ≤ 0.598354795973 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483896974134 : ℝ)) (s := (0.875124973032 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600270803684 : ℝ) ≤ 0.677955170450 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600270803684 : ℝ)) (Q := (0.600270803684 : ℝ))
      (s := (0.799796825603 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773787905877 : ℝ)) (R := (0.774332361988 : ℝ)) (Q2 := (0.600270803684 : ℝ)) (T := (0.823846965440 : ℝ))
    (B := ((84992621483457/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482703292733/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3396916272257319/5000000000000000) := by
  have hk1 : kappa q ≤ 0.597565468340 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482703292733 : ℝ)) (s := (0.875783952345 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599480024406 : ℝ) ≤ 0.677395859570 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599480024406 : ℝ)) (Q := (0.599480024406 : ℝ))
      (s := (0.800389717787 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773277696335 : ℝ)) (R := (0.773822152446 : ℝ)) (Q2 := (0.599480024406 : ℝ)) (T := (0.823507059744 : ℝ))
    (B := ((3396916272257319/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120377402833/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (42426633001249/62500000000000) := by
  have hk1 : kappa q ≤ 0.596776671495 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481509611332 : ℝ)) (s := (0.876440810435 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598689776526 : ℝ) ≤ 0.676837186822 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598689776526 : ℝ)) (Q := (0.598689776526 : ℝ))
      (s := (0.800980993210 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772767493367 : ℝ)) (R := (0.773311949478 : ℝ)) (Q2 := (0.598689776526 : ℝ)) (T := (0.823167401741 : ℝ))
    (B := ((42426633001249/62500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48031592993/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782695204481483/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595988404890 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480315929930 : ℝ)) (s := (0.877095552067 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597900059494 : ℝ) ≤ 0.676279151059 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597900059494 : ℝ)) (Q := (0.597900059494 : ℝ))
      (s := (0.801570657433 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772257296631 : ℝ)) (R := (0.772801752742 : ℝ)) (Q2 := (0.597900059494 : ℝ)) (T := (0.822827991038 : ℝ))
    (B := ((6782695204481483/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479122248529/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1694283813652917/2500000000000000) := by
  have hk1 : kappa q ≤ 0.595200667983 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479122248529 : ℝ)) (s := (0.877748181978 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597110872766 : ℝ) ≤ 0.675721751140 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597110872766 : ℝ)) (Q := (0.597110872766 : ℝ))
      (s := (0.802158715982 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771747105788 : ℝ)) (R := (0.772291561899 : ℝ)) (Q2 := (0.597110872766 : ℝ)) (T := (0.822488827248 : ℝ))
    (B := ((1694283813652917/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12725 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477928567127/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1692895355298791/2500000000000000) := by
  have hk1 : kappa q ≤ 0.594413460232 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477928567127 : ℝ)) (s := (0.878398704874 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596322215801 : ℝ) ≤ 0.675164985929 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596322215801 : ℝ)) (Q := (0.596322215801 : ℝ))
      (s := (0.802745174350 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771236920499 : ℝ)) (R := (0.771781376610 : ℝ)) (Q2 := (0.596322215801 : ℝ)) (T := (0.822149909985 : ℝ))
    (B := ((1692895355298791/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S15
namespace BstLean.Part269.S15
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12725 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052432172377 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S15.wn_upper (by omega : 12725 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010586730027 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035773718421)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010586730027 + 2 * 0.737676 / 12725) := by gcongr
    _ ≤ (0.052432172377 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12725 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12725 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.805141726784 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12725 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.805141726784 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12725 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003470390978 + 0.003286976976 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003470390978 + 0.003286976976 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.805141726784 ≤ R)
    (hB : (X + 0.052432172377 + R + 0.008473053168) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008473053168 := by
    convert (BstLean.Part269.S15.finite_centre_upper (by omega : 12725 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (85348637859/1000000000000)
  | 2 => (86288814071/1000000000000)
  | 3 => (87226759213/1000000000000)
  | 4 => (44081902811/500000000000)
  | 5 => (44550783803/500000000000)
  | 6 => (90041983687/1000000000000)
  | 7 => (90987362879/1000000000000)
  | 8 => (45970217529/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003470390978 + 0.003286976976 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218967570532 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010955772580 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003470390978 + 0.003286976976 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220538989057 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011070626875 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003470390978 + 0.003286976976 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222089881450 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011185101815 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003470390978 + 0.003286976976 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223620457298 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011299205717 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003470390978 + 0.003286976976 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225130920902 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011412946659 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003470390978 + 0.003286976976 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226621469795 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011526332369 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003470390978 + 0.003286976976 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228092296620 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011639370367 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12725 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003470390978 + 0.003286976976 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229543587676 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011752067848 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12725 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g) 1.22 ≤
      minimumGroupCentre g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact uniformFullGroup1 hn hm
  | ⟨2,h⟩ => exact uniformFullGroup2 hn hm
  | ⟨3,h⟩ => exact uniformFullGroup3 hn hm
  | ⟨4,h⟩ => exact uniformFullGroup4 hn hm
  | ⟨5,h⟩ => exact uniformFullGroup5 hn hm
  | ⟨6,h⟩ => exact uniformFullGroup6 hn hm
  | ⟨7,h⟩ => exact uniformFullGroup7 hn hm
  | ⟨8,h⟩ => exact uniformFullGroup8 hn hm
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.S15

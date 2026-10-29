import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S29
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 13075 ≤ n) : wn n ≤ 1.035287484898 := by
  have hnR : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (114.345966260292 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (114.345966260292 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035287484898 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 13075 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 13075 + 24 / (13075 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 13075 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008358394010 : ℝ) := by
  have hnR : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (114.345966260292 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (13075 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035287484898 * (81 / 1000 / 13075)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035287484898 * n *
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
        4 * (1 / 2.506628) * 1.035287484898 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035287484898 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035287484898 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 13075)) / 114.345966260292 := by gcongr
    _ ≤ (0.008358394010 : ℝ) := by norm_num

end BstLean.Part269.S29
namespace BstLean.Part269.S29
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 13075 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 13075 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 13075 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 13075 + 0.008358394010 / 114.345966260292) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 13075 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 13075 := by gcongr
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
  have hn : (114.345966260292 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S29.finite_centre_upper (by omega : 13075 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528086500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7009433875669219/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627954155981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528086500001 : ℝ)) (s := (0.849190584332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629890656525 : ℝ) ≤ 0.699096289081 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629890656525 : ℝ)) (Q := (0.629890656525 : ℝ))
      (s := (0.776683822944 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792676835261 : ℝ)) (R := (0.793206717021 : ℝ)) (Q2 := (0.629890656525 : ℝ)) (T := (0.836593635209 : ℝ))
    (B := ((7009433875669219/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526895150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (437727150190003/625000000000000) := by
  have hk1 : kappa q ≤ 0.627146345960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526895150001 : ℝ)) (s := (0.849930291792 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629081389311 : ℝ) ≤ 0.698513671874 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629081389311 : ℝ)) (Q := (0.629081389311 : ℝ))
      (s := (0.777339440414 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792167125762 : ℝ)) (R := (0.792697007522 : ℝ)) (Q2 := (0.629081389311 : ℝ)) (T := (0.836244959749 : ℝ))
    (B := ((437727150190003/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525703800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6997841422741877/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626339086996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525703800001 : ℝ)) (s := (0.850667687564 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628272673802 : ℝ) ≤ 0.697931735493 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628272673802 : ℝ)) (Q := (0.628272673802 : ℝ))
      (s := (0.777993218065 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791657436127 : ℝ)) (R := (0.792187317887 : ℝ)) (Q2 := (0.628272673802 : ℝ)) (T := (0.835896546552 : ℝ))
    (B := ((6997841422741877/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524512450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1748013730986063/2500000000000000) := by
  have hk1 : kappa q ≤ 0.625532378429 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524512450001 : ℝ)) (s := (0.851402777653 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627464509332 : ℝ) ≤ 0.697350478641 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627464509332 : ℝ)) (Q := (0.627464509332 : ℝ))
      (s := (0.778645162786 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791147765975 : ℝ)) (R := (0.791677647735 : ℝ)) (Q2 := (0.627464509332 : ℝ)) (T := (0.835548395168 : ℝ))
    (B := ((1748013730986063/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523321100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (139725497917193/200000000000000) := by
  have hk1 : kappa q ≤ 0.624726219604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523321100001 : ℝ)) (s := (0.852135568026 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626656895251 : ℝ) ≤ 0.696769900032 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626656895251 : ℝ)) (Q := (0.626656895251 : ℝ))
      (s := (0.779295281415 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790638114932 : ℝ)) (R := (0.791167996692 : ℝ)) (Q2 := (0.626656895251 : ℝ)) (T := (0.835200505154 : ℝ))
    (B := ((139725497917193/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522129750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (872562665967901/1250000000000000) := by
  have hk1 : kappa q ≤ 0.623920609872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522129750001 : ℝ)) (s := (0.852866064611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625849830904 : ℝ) ≤ 0.696189998380 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625849830904 : ℝ)) (Q := (0.625849830904 : ℝ))
      (s := (0.779943580753 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790128482622 : ℝ)) (R := (0.790658364382 : ℝ)) (Q2 := (0.625849830904 : ℝ)) (T := (0.834852876067 : ℝ))
    (B := ((872562665967901/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520938400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6974734208892459/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623115548582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520938400001 : ℝ)) (s := (0.853594273297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625043315641 : ℝ) ≤ 0.695610772404 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625043315641 : ℝ)) (Q := (0.625043315641 : ℝ))
      (s := (0.780590067560 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789618868671 : ℝ)) (R := (0.790148750431 : ℝ)) (Q2 := (0.625043315641 : ℝ)) (T := (0.834505507463 : ℝ))
    (B := ((6974734208892459/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519747050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3484486764323531/5000000000000000) := by
  have hk1 : kappa q ≤ 0.622311035089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519747050001 : ℝ)) (s := (0.854320199934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624237348815 : ℝ) ≤ 0.695032220826 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624237348815 : ℝ)) (Q := (0.624237348815 : ℝ))
      (s := (0.781234748552 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789109272704 : ℝ)) (R := (0.789639154464 : ℝ)) (Q2 := (0.624237348815 : ℝ)) (T := (0.834158398902 : ℝ))
    (B := ((3484486764323531/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518555700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392643855277709/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621507068752 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518555700001 : ℝ)) (s := (0.855043850336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623431929785 : ℝ) ≤ 0.694454342377 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623431929785 : ℝ)) (Q := (0.623431929785 : ℝ))
      (s := (0.781877630403 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788599694351 : ℝ)) (R := (0.789129576111 : ℝ)) (Q2 := (0.623431929785 : ℝ)) (T := (0.833811549945 : ℝ))
    (B := ((1392643855277709/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517364350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1739367860385011/2500000000000000) := by
  have hk1 : kappa q ≤ 0.620703648931 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517364350001 : ℝ)) (s := (0.855765230276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622627057910 : ℝ) ≤ 0.693877135785 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622627057910 : ℝ)) (Q := (0.622627057910 : ℝ))
      (s := (0.782518719750 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788090133240 : ℝ)) (R := (0.788620015000 : ℝ)) (Q2 := (0.622627057910 : ℝ)) (T := (0.833464960154 : ℝ))
    (B := ((1739367860385011/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516173000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6951730013566041/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619900774988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516173000001 : ℝ)) (s := (0.856484345491 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621822732548 : ℝ) ≤ 0.693300599784 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621822732548 : ℝ)) (Q := (0.621822732548 : ℝ))
      (s := (0.783158023190 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787580588998 : ℝ)) (R := (0.788110470758 : ℝ)) (Q2 := (0.621822732548 : ℝ)) (T := (0.833118629091 : ℝ))
    (B := ((6951730013566041/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514981650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6945994981972111/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619098446292 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514981650001 : ℝ)) (s := (0.857201201681 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621018953072 : ℝ) ≤ 0.692724733118 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621018953072 : ℝ)) (Q := (0.621018953072 : ℝ))
      (s := (0.783795547274 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787071061259 : ℝ)) (R := (0.787600943019 : ℝ)) (Q2 := (0.621018953072 : ℝ)) (T := (0.832772556324 : ℝ))
    (B := ((6945994981972111/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513790300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940266336304673/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618296662211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513790300001 : ℝ)) (s := (0.857915804509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620215718843 : ℝ) ≤ 0.692149534524 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620215718843 : ℝ)) (Q := (0.620215718843 : ℝ))
      (s := (0.784431298522 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786561549651 : ℝ)) (R := (0.787091431411 : ℝ)) (Q2 := (0.620215718843 : ℝ)) (T := (0.832426741416 : ℝ))
    (B := ((6940266336304673/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512598950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (693454406615073/1000000000000000) := by
  have hk1 : kappa q ≤ 0.617495422118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512598950001 : ℝ)) (s := (0.858628159600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619413029238 : ℝ) ≤ 0.691575002754 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619413029238 : ℝ)) (Q := (0.619413029238 : ℝ))
      (s := (0.785065283407 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786052053809 : ℝ)) (R := (0.786581935569 : ℝ)) (Q2 := (0.619413029238 : ℝ)) (T := (0.832081183937 : ℝ))
    (B := ((693454406615073/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511407600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1732207040284407/2500000000000000) := by
  have hk1 : kappa q ≤ 0.616694725391 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511407600001 : ℝ)) (s := (0.859338272546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618610883630 : ℝ) ≤ 0.691001136558 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618610883630 : ℝ)) (Q := (0.618610883630 : ℝ))
      (s := (0.785697508368 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785542573365 : ℝ)) (R := (0.786072455125 : ℝ)) (Q2 := (0.618610883630 : ℝ)) (T := (0.831735883455 : ℝ))
    (B := ((1732207040284407/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510216250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1730779652733201/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615894571407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510216250001 : ℝ)) (s := (0.860046148899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617809281398 : ℝ) ≤ 0.690427934691 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617809281398 : ℝ)) (Q := (0.617809281398 : ℝ))
      (s := (0.786327979802 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785033107955 : ℝ)) (R := (0.785562989715 : ℝ)) (Q2 := (0.617809281398 : ℝ)) (T := (0.831390839543 : ℝ))
    (B := ((1730779652733201/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509024900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (864676925655443/1250000000000000) := by
  have hk1 : kappa q ≤ 0.615094959549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509024900001 : ℝ)) (s := (0.860751794178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617008221921 : ℝ) ≤ 0.689855395913 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617008221921 : ℝ)) (Q := (0.617008221921 : ℝ))
      (s := (0.786956704071 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784523657213 : ℝ)) (R := (0.785053538973 : ℝ)) (Q2 := (0.617008221921 : ℝ)) (T := (0.831046051771 : ℝ))
    (B := ((864676925655443/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507833550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6911718533816741/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614295889201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507833550001 : ℝ)) (s := (0.861455213864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616207704585 : ℝ) ≤ 0.689283518989 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616207704585 : ℝ)) (Q := (0.616207704585 : ℝ))
      (s := (0.787583687497 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784014220776 : ℝ)) (R := (0.784544102536 : ℝ)) (Q2 := (0.616207704585 : ℝ)) (T := (0.830701519716 : ℝ))
    (B := ((6911718533816741/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506642200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906027986438651/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613497359753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506642200001 : ℝ)) (s := (0.862156413407 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615407728777 : ℝ) ≤ 0.688712302686 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615407728777 : ℝ)) (Q := (0.615407728777 : ℝ))
      (s := (0.788208936363 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783504798282 : ℝ)) (R := (0.784034680042 : ℝ)) (Q2 := (0.615407728777 : ℝ)) (T := (0.830357242951 : ℝ))
    (B := ((6906027986438651/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505450850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450171876467329/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612699370595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505450850001 : ℝ)) (s := (0.862855398218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614608293886 : ℝ) ≤ 0.688141745775 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614608293886 : ℝ)) (Q := (0.614608293886 : ℝ))
      (s := (0.788832456918 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782995389369 : ℝ)) (R := (0.783525271129 : ℝ)) (Q2 := (0.614608293886 : ℝ)) (T := (0.830013221054 : ℝ))
    (B := ((3450171876467329/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504259500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447332911584519/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611901921122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504259500001 : ℝ)) (s := (0.863552173675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613809399308 : ℝ) ≤ 0.687571847036 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613809399308 : ℝ)) (Q := (0.613809399308 : ℝ))
      (s := (0.789454255370 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782485993677 : ℝ)) (R := (0.783015875437 : ℝ)) (Q2 := (0.613809399308 : ℝ)) (T := (0.829669453605 : ℝ))
    (B := ((3447332911584519/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503068150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444497093522361/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611105010733 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503068150001 : ℝ)) (s := (0.864246745123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613011044438 : ℝ) ≤ 0.687002605246 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613011044438 : ℝ)) (Q := (0.613011044438 : ℝ))
      (s := (0.790074337893 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781976610847 : ℝ)) (R := (0.782506492607 : ℝ)) (Q2 := (0.613011044438 : ℝ)) (T := (0.829325940183 : ℝ))
    (B := ((3444497093522361/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501876800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883328834503063/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610308638826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501876800001 : ℝ)) (s := (0.864939117870 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612213228673 : ℝ) ≤ 0.686434019190 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612213228673 : ℝ)) (Q := (0.612213228673 : ℝ))
      (s := (0.790692710627 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781467240519 : ℝ)) (R := (0.781997122279 : ℝ)) (Q2 := (0.612213228673 : ℝ)) (T := (0.828982680370 : ℝ))
    (B := ((6883328834503063/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500685450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6877669755523611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609512804807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500685450001 : ℝ)) (s := (0.865629297193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611415951421 : ℝ) ≤ 0.685866087660 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611415951421 : ℝ)) (Q := (0.611415951421 : ℝ))
      (s := (0.791309379667 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780957882338 : ℝ)) (R := (0.781487764098 : ℝ)) (Q2 := (0.611415951421 : ℝ)) (T := (0.828639673751 : ℝ))
    (B := ((6877669755523611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499494100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872016940123879/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608717508081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499494100001 : ℝ)) (s := (0.866317288333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610619212083 : ℝ) ≤ 0.685298809445 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610619212083 : ℝ)) (Q := (0.610619212083 : ℝ))
      (s := (0.791924351082 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780448535946 : ℝ)) (R := (0.780978417706 : ℝ)) (Q2 := (0.610619212083 : ℝ)) (T := (0.828296919909 : ℝ))
    (B := ((6872016940123879/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498302750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866370378359119/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607922748060 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498302750001 : ℝ)) (s := (0.867003096501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609823010071 : ℝ) ≤ 0.684732183345 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609823010071 : ℝ)) (Q := (0.609823010071 : ℝ))
      (s := (0.792537630898 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779939200989 : ℝ)) (R := (0.780469082749 : ℝ)) (Q2 := (0.609823010071 : ℝ)) (T := (0.827954418432 : ℝ))
    (B := ((6866370378359119/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497111400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6860730060322097/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607128524156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497111400001 : ℝ)) (s := (0.867686726872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609027344796 : ℝ) ≤ 0.684166208161 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609027344796 : ℝ)) (Q := (0.609027344796 : ℝ))
      (s := (0.793149225109 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779429877112 : ℝ)) (R := (0.779959758872 : ℝ)) (Q2 := (0.609027344796 : ℝ)) (T := (0.827612168908 : ℝ))
    (B := ((6860730060322097/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495920050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855095976142871/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606334835785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495920050001 : ℝ)) (s := (0.868368184590 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608232215672 : ℝ) ≤ 0.683600882698 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608232215672 : ℝ)) (Q := (0.608232215672 : ℝ))
      (s := (0.793759139676 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778920563962 : ℝ)) (R := (0.779450445722 : ℝ)) (Q2 := (0.608232215672 : ℝ)) (T := (0.827270170928 : ℝ))
    (B := ((6855095976142871/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494728700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849468115988569/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605541682366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494728700001 : ℝ)) (s := (0.869047474765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607437622119 : ℝ) ≤ 0.683036205767 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607437622119 : ℝ)) (Q := (0.607437622119 : ℝ))
      (s := (0.794367380521 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778411261188 : ℝ)) (R := (0.778941142948 : ℝ)) (Q2 := (0.607437622119 : ℝ)) (T := (0.826928424083 : ℝ))
    (B := ((6849468115988569/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493537350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6843846470063171/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604749063323 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493537350001 : ℝ)) (s := (0.869724602478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606643563559 : ℝ) ≤ 0.682472176183 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606643563559 : ℝ)) (Q := (0.606643563559 : ℝ))
      (s := (0.794973953531 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777901968439 : ℝ)) (R := (0.778431850199 : ℝ)) (Q2 := (0.606643563559 : ℝ)) (T := (0.826586927968 : ℝ))
    (B := ((6843846470063171/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492346000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1709557757151823/2500000000000000) := by
  have hk1 : kappa q ≤ 0.603956978079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492346000001 : ℝ)) (s := (0.870399572773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605850039413 : ℝ) ≤ 0.681908792761 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605850039413 : ℝ)) (Q := (0.605850039413 : ℝ))
      (s := (0.795578864566 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777392685364 : ℝ)) (R := (0.777922567124 : ℝ)) (Q2 := (0.605850039413 : ℝ)) (T := (0.826245682175 : ℝ))
    (B := ((1709557757151823/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491154650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1366524356379593/2000000000000000) := by
  have hk1 : kappa q ≤ 0.603165426065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491154650001 : ℝ)) (s := (0.871072390668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605057049113 : ℝ) ≤ 0.681346054328 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605057049113 : ℝ)) (Q := (0.605057049113 : ℝ))
      (s := (0.796182119442 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776883411616 : ℝ)) (R := (0.777413293376 : ℝ)) (Q2 := (0.605057049113 : ℝ)) (T := (0.825904686304 : ℝ))
    (B := ((1366524356379593/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489963300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (682701872024843/1000000000000000) := by
  have hk1 : kappa q ≤ 0.602374406710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489963300001 : ℝ)) (s := (0.871743061144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604264592086 : ℝ) ≤ 0.680783959709 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604264592086 : ℝ)) (Q := (0.604264592086 : ℝ))
      (s := (0.796783723950 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776374146845 : ℝ)) (R := (0.776904028605 : ℝ)) (Q2 := (0.604264592086 : ℝ)) (T := (0.825563939951 : ℝ))
    (B := ((682701872024843/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488771950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3410710917003961/5000000000000000) := by
  have hk1 : kappa q ≤ 0.601583919451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488771950001 : ℝ)) (s := (0.872411589156 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603472667767 : ℝ) ≤ 0.680222507735 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603472667767 : ℝ)) (Q := (0.603472667767 : ℝ))
      (s := (0.797383683843 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775864890706 : ℝ)) (R := (0.776394772466 : ℝ)) (Q2 := (0.603472667767 : ℝ)) (T := (0.825223442718 : ℝ))
    (B := ((3410710917003961/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487580600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6815831113561457/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600793963725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487580600001 : ℝ)) (s := (0.873077979624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602681275592 : ℝ) ≤ 0.679661697240 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602681275592 : ℝ)) (Q := (0.602681275592 : ℝ))
      (s := (0.797982004842 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775355642853 : ℝ)) (R := (0.775885524613 : ℝ)) (Q2 := (0.602681275592 : ℝ)) (T := (0.824883194204 : ℝ))
    (B := ((6815831113561457/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486389250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810246549329631/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600004538972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486389250001 : ℝ)) (s := (0.873742237439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601890415001 : ℝ) ≤ 0.679101527066 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601890415001 : ℝ)) (Q := (0.601890415001 : ℝ))
      (s := (0.798578692635 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774846402941 : ℝ)) (R := (0.775376284701 : ℝ)) (Q2 := (0.601890415001 : ℝ)) (T := (0.824543194015 : ℝ))
    (B := ((6810246549329631/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485197900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402334065884203/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599215644636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485197900001 : ℝ)) (s := (0.874404367461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601100085437 : ℝ) ≤ 0.678541996056 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601100085437 : ℝ)) (Q := (0.601100085437 : ℝ))
      (s := (0.799173752878 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774337170627 : ℝ)) (R := (0.774867052387 : ℝ)) (Q2 := (0.601100085437 : ℝ)) (T := (0.824203441755 : ℝ))
    (B := ((3402334065884203/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484006550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (679909585136891/1000000000000000) := by
  have hk1 : kappa q ≤ 0.598427280166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484006550001 : ℝ)) (s := (0.875064374522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600310286349 : ℝ) ≤ 0.677983103060 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600310286349 : ℝ)) (Q := (0.600310286349 : ℝ))
      (s := (0.799767191190 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773827945570 : ℝ)) (R := (0.774357827330 : ℝ)) (Q2 := (0.600310286349 : ℝ)) (T := (0.823863937033 : ℝ))
    (B := ((679909585136891/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482815200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793529698657233/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597639445009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482815200001 : ℝ)) (s := (0.875722263420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599521017180 : ℝ) ≤ 0.677424846926 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599521017180 : ℝ)) (Q := (0.599521017180 : ℝ))
      (s := (0.800359013169 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773318727426 : ℝ)) (R := (0.773848609186 : ℝ)) (Q2 := (0.599521017180 : ℝ)) (T := (0.823524679454 : ℝ))
    (B := ((6793529698657233/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481623850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (424248104012139/625000000000000) := by
  have hk1 : kappa q ≤ 0.596852138620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481623850001 : ℝ)) (s := (0.876378038926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598732277387 : ℝ) ≤ 0.676867226515 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598732277387 : ℝ)) (Q := (0.598732277387 : ℝ))
      (s := (0.800949224368 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772809515857 : ℝ)) (R := (0.773339397617 : ℝ)) (Q2 := (0.598732277387 : ℝ)) (T := (0.823185668631 : ℝ))
    (B := ((424248104012139/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480432500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782415738575293/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596065360454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480432500001 : ℝ)) (s := (0.877031705780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597944066422 : ℝ) ≤ 0.676310240685 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597944066422 : ℝ)) (Q := (0.597944066422 : ℝ))
      (s := (0.801537830318 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772300310522 : ℝ)) (R := (0.772830192282 : ℝ)) (Q2 := (0.597944066422 : ℝ)) (T := (0.822846904175 : ℝ))
    (B := ((6782415738575293/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479241150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1694216978107553/2500000000000000) := by
  have hk1 : kappa q ≤ 0.595279109971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479241150001 : ℝ)) (s := (0.877683268695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597156383746 : ℝ) ≤ 0.675753888303 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597156383746 : ℝ)) (Q := (0.597156383746 : ℝ))
      (s := (0.802124836514 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771791111085 : ℝ)) (R := (0.772320992845 : ℝ)) (Q2 := (0.597156383746 : ℝ)) (T := (0.822508385700 : ℝ))
    (B := ((1694216978107553/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 13075 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478049800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385663088211459/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594493386633 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478049800001 : ℝ)) (s := (0.878332732351 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596369228818 : ℝ) ≤ 0.675198168237 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596369228818 : ℝ)) (Q := (0.596369228818 : ℝ))
      (s := (0.802710248421 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771281917208 : ℝ)) (R := (0.771811798968 : ℝ)) (Q2 := (0.596369228818 : ℝ)) (T := (0.822170112822 : ℝ))
    (B := ((3385663088211459/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S29
namespace BstLean.Part269.S29
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 13075 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.051718092417 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S29.wn_upper (by omega : 13075 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010444072670 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035287484898)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010444072670 + 2 * 0.737676 / 13075) := by gcongr
    _ ≤ (0.051718092417 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 13075 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 13075 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.345966260292 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (13075 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (114.345966260292 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 13075 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003177634099 + 0.003195984085 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003177634099 + 0.003195984085 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.345966260292 ≤ R)
    (hB : (X + 0.051718092417 + R + 0.008358394010) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008358394010 := by
    convert (BstLean.Part269.S29.finite_centre_upper (by omega : 13075 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (16880942493/200000000000)
  | 2 => (21332524561/250000000000)
  | 3 => (86251204671/1000000000000)
  | 4 => (10896110117/125000000000)
  | 5 => (344078791/3906250000)
  | 6 => (3559933677/40000000000)
  | 7 => (89912923049/1000000000000)
  | 8 => (45414869241/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003177634099 + 0.003195984085 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218199160519 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010808142334 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003177634099 + 0.003195984085 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.219774583515 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010921448954 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003177634099 + 0.003195984085 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221329352923 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011034381332 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003177634099 + 0.003195984085 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.222863682781 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011146947671 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003177634099 + 0.003195984085 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224377781620 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011259155941 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003177634099 + 0.003195984085 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.225871850987 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011371013767 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003177634099 + 0.003195984085 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227346087345 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011482528565 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 13075 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003177634099 + 0.003195984085 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.228800680626 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011593707435 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 13075 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g) :
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

end BstLean.Part269.S29

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S17
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12775 ≤ n) : wn n ≤ 1.035703027963 := by
  have hnR : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.026545554573 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.026545554573 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035703027963 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12775 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12775 + 24 / (12775 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12775 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008456384432 : ℝ) := by
  have hnR : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.026545554573 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12775 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035703027963 * (81 / 1000 / 12775)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035703027963 * n *
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
        4 * (1 / 2.506628) * 1.035703027963 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035703027963 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035703027963 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12775)) / 113.026545554573 := by gcongr
    _ ≤ (0.008456384432 : ℝ) := by norm_num

end BstLean.Part269.S17
namespace BstLean.Part269.S17
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12775 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12775 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12775 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12775 + 0.008456384432 / 113.026545554573) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12775 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12775 := by gcongr
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
  have hn : (113.026545554573 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S17.finite_centre_upper (by omega : 12775 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4224547919/8000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010074040641773/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627941939880 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528068489875 : ℝ)) (s := (0.849201784031 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629907177730 : ℝ) ≤ 0.699108186181 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629907177730 : ℝ)) (Q := (0.629907177730 : ℝ))
      (s := (0.776670423954 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792674794171 : ℝ)) (R := (0.793217119338 : ℝ)) (Q2 := (0.629907177730 : ℝ)) (T := (0.836600753682 : ℝ))
    (B := ((7010074040641773/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263437669431/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502132640168329/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627132917425 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526875338862 : ℝ)) (s := (0.849942572942 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629096683174 : ℝ) ≤ 0.698524679779 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629096683174 : ℝ)) (Q := (0.629096683174 : ℝ))
      (s := (0.777327063224 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792164318092 : ℝ)) (R := (0.792706643259 : ℝ)) (Q2 := (0.629096683174 : ℝ)) (T := (0.836251548932 : ℝ))
    (B := ((3502132640168329/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (10513643757/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1749615758147567/2500000000000000) := by
  have hk1 : kappa q ≤ 0.626324447684 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525682187850 : ℝ)) (s := (0.850681043270 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628286741981 : ℝ) ≤ 0.697941856267 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628286741981 : ℝ)) (Q := (0.628286741981 : ℝ))
      (s := (0.777981857020 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791653861935 : ℝ)) (R := (0.792196187102 : ℝ)) (Q2 := (0.628286741981 : ℝ)) (T := (0.835902607237 : ℝ))
    (B := ((1749615758147567/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524489036837/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (699266728652179/1000000000000000) := by
  have hk1 : kappa q ≤ 0.625516529992 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524489036837 : ℝ)) (s := (0.851417201047 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477353486 : ℝ) ≤ 0.697359714342 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477353486 : ℝ)) (Q := (0.627477353486 : ℝ))
      (s := (0.778634812260 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791143425319 : ℝ)) (R := (0.791685750486 : ℝ)) (Q2 := (0.627477353486 : ℝ)) (T := (0.835553928146 : ℝ))
    (B := ((699266728652179/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1022062277/1953125000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986878031293609/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624709163693 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523295885824 : ℝ)) (s := (0.852151052267 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668517029 : ℝ) ≤ 0.696778252709 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668517029 : ℝ)) (Q := (0.626668517029 : ℝ))
      (s := (0.779285935819 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790633007865 : ℝ)) (R := (0.791175333032 : ℝ)) (Q2 := (0.626668517029 : ℝ)) (T := (0.835205511211 : ℝ))
    (B := ((6986878031293609/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130525683703/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3490547628055517/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623902348135 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522102734812 : ℝ)) (s := (0.852882602884 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625860231960 : ℝ) ≤ 0.696197470082 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625860231960 : ℝ)) (Q := (0.625860231960 : ℝ))
      (s := (0.779935234524 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790122609200 : ℝ)) (R := (0.790664934367 : ℝ)) (Q2 := (0.625860231960 : ℝ)) (T := (0.834857355990 : ℝ))
    (B := ((3490547628055517/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520909583799/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975318950222031/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623096082664 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520909583799 : ℝ)) (s := (0.853611858814 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625052497621 : ℝ) ≤ 0.695617365170 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625052497621 : ℝ)) (Q := (0.625052497621 : ℝ))
      (s := (0.780582715168 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789612228944 : ℝ)) (R := (0.790154554111 : ℝ)) (Q2 := (0.625052497621 : ℝ)) (T := (0.834509462036 : ℝ))
    (B := ((6975318950222031/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519716432787/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969549102916953/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622290366632 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519716432787 : ℝ)) (s := (0.854338825930 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624245313363 : ℝ) ≤ 0.695037936690 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624245313363 : ℝ)) (Q := (0.624245313363 : ℝ))
      (s := (0.781228384498 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789101866723 : ℝ)) (R := (0.789644191890 : ℝ)) (Q2 := (0.624245313363 : ℝ)) (T := (0.834161828905 : ℝ))
    (B := ((6969549102916953/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259261640887/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1740946425882069/2500000000000000) := by
  have hk1 : kappa q ≤ 0.621485199394 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518523281774 : ℝ)) (s := (0.855063510073 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623438678541 : ℝ) ≤ 0.694459183366 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623438678541 : ℝ)) (Q := (0.623438678541 : ℝ))
      (s := (0.781872249220 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788591522163 : ℝ)) (R := (0.789133847330 : ℝ)) (Q2 := (0.623438678541 : ℝ)) (T := (0.833814456159 : ℝ))
    (B := ((1740946425882069/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517330130761/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3479014370715171/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620680580308 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517330130761 : ℝ)) (s := (0.855785917042 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622632592511 : ℝ) ≤ 0.693881103922 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622632592511 : ℝ)) (Q := (0.622632592511 : ℝ))
      (s := (0.782514315999 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788081194891 : ℝ)) (R := (0.788623520058 : ℝ)) (Q2 := (0.622632592511 : ℝ)) (T := (0.833467343356 : ℝ))
    (B := ((3479014370715171/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516136979749/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (695227820603909/1000000000000000) := by
  have hk1 : kappa q ≤ 0.619876508735 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516136979749 : ℝ)) (s := (0.856506052598 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621827054636 : ℝ) ≤ 0.693303697089 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621827054636 : ℝ)) (Q := (0.621827054636 : ℝ))
      (s := (0.783154591459 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787570884536 : ℝ)) (R := (0.788113209703 : ℝ)) (Q2 := (0.621827054636 : ℝ)) (T := (0.833120490059 : ℝ))
    (B := ((695227820603909/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2011499331/3906250000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (217079190212869/312500000000000) := by
  have hk1 : kappa q ≤ 0.619072984038 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514943828736 : ℝ)) (s := (0.857223922466 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621022064273 : ℝ) ≤ 0.692726961598 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621022064273 : ℝ)) (Q := (0.621022064273 : ℝ))
      (s := (0.783793082189 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787060590724 : ℝ)) (R := (0.787602915891 : ℝ)) (Q2 := (0.621022064273 : ℝ)) (T := (0.832773895828 : ℝ))
    (B := ((217079190212869/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128437669431/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (867599546655859/1250000000000000) := by
  have hk1 : kappa q ≤ 0.618270005585 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513750677724 : ℝ)) (s := (0.857939532333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620217620793 : ℝ) ≤ 0.692150896189 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620217620793 : ℝ)) (Q := (0.620217620793 : ℝ))
      (s := (0.784429794729 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786550313088 : ℝ)) (R := (0.787092638255 : ℝ)) (Q2 := (0.620217620793 : ℝ)) (T := (0.832427560231 : ℝ))
    (B := ((867599546655859/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512557526711/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1733766263720873/2500000000000000) := by
  have hk1 : kappa q ≤ 0.617467572745 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512557526711 : ℝ)) (s := (0.858652887850 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619413723561 : ℝ) ≤ 0.691575499602 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619413723561 : ℝ)) (Q := (0.619413723561 : ℝ))
      (s := (0.785064735589 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786040051256 : ℝ)) (R := (0.786582376423 : ℝ)) (Q2 := (0.619413723561 : ℝ)) (T := (0.832081482833 : ℝ))
    (B := ((1733766263720873/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511364375699/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929340121301467/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616665684893 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511364375699 : ℝ)) (s := (0.859363994630 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618610371952 : ℝ) ≤ 0.691000770584 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618610371952 : ℝ)) (Q := (0.618610371952 : ℝ))
      (s := (0.785697911232 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785529804862 : ℝ)) (R := (0.786072130029 : ℝ)) (Q2 := (0.618610371952 : ℝ)) (T := (0.831735663200 : ℝ))
    (B := ((6929340121301467/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255085612343/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1730905390530233/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615864341403 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510171224686 : ℝ)) (s := (0.860072858253 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617807565339 : ℝ) ≤ 0.690426707884 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617807565339 : ℝ)) (Q := (0.617807565339 : ℝ))
      (s := (0.786329328088 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785019573537 : ℝ)) (R := (0.785561898704 : ℝ)) (Q2 := (0.617807565339 : ℝ)) (T := (0.831390100902 : ℝ))
    (B := ((1730905390530233/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508978073673/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (691790936700211/1000000000000000) := by
  have hk1 : kappa q ≤ 0.615063541657 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508978073673 : ℝ)) (s := (0.860779484259 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617005303103 : ℝ) ≤ 0.689853310258 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617005303103 : ℝ)) (Q := (0.617005303103 : ℝ))
      (s := (0.786958992543 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784509356917 : ℝ)) (R := (0.785051682084 : ℝ)) (Q2 := (0.617005303103 : ℝ)) (T := (0.831044795510 : ℝ))
    (B := ((691790936700211/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507784922661/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (432012720352817/625000000000000) := by
  have hk1 : kappa q ≤ 0.614263285036 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507784922661 : ℝ)) (s := (0.861483878154 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616203584624 : ℝ) ≤ 0.689280576463 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616203584624 : ℝ)) (Q := (0.616203584624 : ℝ))
      (s := (0.787586910948 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783999154636 : ℝ)) (R := (0.784541479803 : ℝ)) (Q2 := (0.616203584624 : ℝ)) (T := (0.830699746597 : ℝ))
    (B := ((432012720352817/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494718527/976562500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1726626006947373/2500000000000000) := by
  have hk1 : kappa q ≤ 0.613463570925 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506591771648 : ℝ)) (s := (0.862186045410 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615402409284 : ℝ) ≤ 0.688708505260 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615402409284 : ℝ)) (Q := (0.615402409284 : ℝ))
      (s := (0.788213089620 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783488966328 : ℝ)) (R := (0.784031291495 : ℝ)) (Q2 := (0.615402409284 : ℝ)) (T := (0.830354953734 : ℝ))
    (B := ((1726626006947373/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126349655159/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (862601357901801/1250000000000000) := by
  have hk1 : kappa q ≤ 0.612664398714 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505398620636 : ℝ)) (s := (0.862885991461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614601776475 : ℝ) ≤ 0.688137095419 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614601776475 : ℝ)) (Q := (0.614601776475 : ℝ))
      (s := (0.788837534829 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782978791633 : ℝ)) (R := (0.783521116800 : ℝ)) (Q2 := (0.614601776475 : ℝ)) (T := (0.830010416498 : ℝ))
    (B := ((862601357901801/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504205469623/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895124021737983/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611865767795 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504205469623 : ℝ)) (s := (0.863583721710 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613801685586 : ℝ) ≤ 0.687566345709 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613801685586 : ℝ)) (Q := (0.613801685586 : ℝ))
      (s := (0.789460252814 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782468630188 : ℝ)) (R := (0.783010955355 : ℝ)) (Q2 := (0.613801685586 : ℝ)) (T := (0.829666134467 : ℝ))
    (B := ((6895124021737983/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503012318611/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889443493217269/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611067677562 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503012318611 : ℝ)) (s := (0.864279241522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613002136010 : ℝ) ≤ 0.686996254905 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613002136010 : ℝ)) (Q := (0.613002136010 : ℝ))
      (s := (0.790081249776 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781958481631 : ℝ)) (R := (0.782500806798 : ℝ)) (Q2 := (0.613002136010 : ℝ)) (T := (0.829322107218 : ℝ))
    (B := ((6889443493217269/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250909583799/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883769267547973/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610270127414 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501819167598 : ℝ)) (s := (0.864972556231 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612203127147 : ℝ) ≤ 0.686426821789 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612203127147 : ℝ)) (Q := (0.612203127147 : ℝ))
      (s := (0.790700531878 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781448345604 : ℝ)) (R := (0.781990670771 : ℝ)) (Q2 := (0.612203127147 : ℝ)) (T := (0.828978334332 : ℝ))
    (B := ((6883769267547973/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100125203317/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (275124053386569/400000000000000) := by
  have hk1 : kappa q ≤ 0.609473116751 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500626016585 : ℝ)) (s := (0.865663671133 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611404658393 : ℝ) ≤ 0.685858045141 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611404658393 : ℝ)) (Q := (0.611404658393 : ℝ))
      (s := (0.791318105250 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780938221746 : ℝ)) (R := (0.781480546913 : ℝ)) (Q2 := (0.611404658393 : ℝ)) (T := (0.828634815390 : ℝ))
    (B := ((275124053386569/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499432865573/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872439684538349/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608676644979 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499432865573 : ℝ)) (s := (0.866352591493 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610606729155 : ℝ) ≤ 0.685289923751 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610606729155 : ℝ)) (Q := (0.610606729155 : ℝ))
      (s := (0.791933975980 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780428109702 : ℝ)) (R := (0.780970434869 : ℝ)) (Q2 := (0.610606729155 : ℝ)) (T := (0.828291549976 : ℝ))
    (B := ((6872439684538349/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (389249777/781250000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (858348038397579/1250000000000000) := by
  have hk1 : kappa q ≤ 0.607880711504 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498239714560 : ℝ)) (s := (0.867039322543 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609809338836 : ℝ) ≤ 0.684722456409 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609809338836 : ℝ)) (Q := (0.609809338836 : ℝ))
      (s := (0.792548150127 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779918009112 : ℝ)) (R := (0.780460334279 : ℝ)) (Q2 := (0.609809338836 : ℝ)) (T := (0.827948537674 : ℝ))
    (B := ((858348038397579/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (124261640887/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (68611351926391/100000000000000) := by
  have hk1 : kappa q ≤ 0.607085315738 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497046563548 : ℝ)) (s := (0.867723869480 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609012486848 : ℝ) ≤ 0.684155641913 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609012486848 : ℝ)) (Q := (0.609012486848 : ℝ))
      (s := (0.793160633708 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779407919623 : ℝ)) (R := (0.779950244790 : ℝ)) (Q2 := (0.609012486848 : ℝ)) (T := (0.827605778072 : ℝ))
    (B := ((68611351926391/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99170682507/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1371098466199859/2000000000000000) := by
  have hk1 : kappa q ≤ 0.606290457093 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495853412535 : ℝ)) (s := (0.868406237471 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608216172602 : ℝ) ≤ 0.683589479063 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608216172602 : ℝ)) (Q := (0.608216172602 : ℝ))
      (s := (0.793771432710 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778897840879 : ℝ)) (R := (0.779440166046 : ℝ)) (Q2 := (0.608216172602 : ℝ)) (T := (0.827263270757 : ℝ))
    (B := ((1371098466199859/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247330130761/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (136997114247681/200000000000000) := by
  have hk1 : kappa q ≤ 0.605496134987 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494660261522 : ℝ)) (s := (0.869086431646 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607420395515 : ℝ) ≤ 0.683023966665 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607420395515 : ℝ)) (Q := (0.607420395515 : ℝ))
      (s := (0.794380553081 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778387772527 : ℝ)) (R := (0.778930097694 : ℝ)) (Q2 := (0.607420395515 : ℝ)) (T := (0.826921015321 : ℝ))
    (B := ((136997114247681/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49346711051/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844225326953267/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604702348840 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493467110510 : ℝ)) (s := (0.869764457107 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606625155008 : ℝ) ≤ 0.682459103528 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606625155008 : ℝ)) (Q := (0.606625155008 : ℝ))
      (s := (0.794988000735 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777877714216 : ℝ)) (R := (0.778420039383 : ℝ)) (Q2 := (0.606625155008 : ℝ)) (T := (0.826579011354 : ℝ))
    (B := ((6844225326953267/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492273959497/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838601164903703/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603909098073 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492273959497 : ℝ)) (s := (0.870440318920 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605830450497 : ℝ) ≤ 0.681894888461 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605830450497 : ℝ)) (Q := (0.605830450497 : ℝ))
      (s := (0.795593781557 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777367665591 : ℝ)) (R := (0.777909990758 : ℝ)) (Q2 := (0.605830450497 : ℝ)) (T := (0.826237258448 : ℝ))
    (B := ((6838601164903703/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (98216161697/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (218655462927/320000000000) := by
  have hk1 : kappa q ≤ 0.603116382116 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491080808485 : ℝ)) (s := (0.871114022123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605036281413 : ℝ) ≤ 0.681331320288 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605036281413 : ℝ)) (Q := (0.605036281413 : ℝ))
      (s := (0.796197901388 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776857626306 : ℝ)) (R := (0.777399951473 : ℝ)) (Q2 := (0.605036281413 : ℝ)) (T := (0.825895756202 : ℝ))
    (B := ((218655462927/320000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (956811831/1953125000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827371471918221/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602324200394 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489887657472 : ℝ)) (s := (0.871785571719 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604242647179 : ℝ) ≤ 0.680768397825 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604242647179 : ℝ)) (Q := (0.604242647179 : ℝ))
      (s := (0.796800366046 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776347596008 : ℝ)) (R := (0.776889921175 : ℝ)) (Q2 := (0.604242647179 : ℝ)) (T := (0.825554504209 : ℝ))
    (B := ((6827371471918221/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24434725323/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364353184311627/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601532552342 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488694506460 : ℝ)) (s := (0.872454972682 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603449547231 : ℝ) ≤ 0.680206119902 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603449547231 : ℝ)) (Q := (0.603449547231 : ℝ))
      (s := (0.797401181306 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775837574351 : ℝ)) (R := (0.776379899518 : ℝ)) (Q2 := (0.603449547231 : ℝ)) (T := (0.825213502069 : ℝ))
    (B := ((1364353184311627/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487501355447/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816166555730509/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600741437394 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487501355447 : ℝ)) (s := (0.873122229953 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602656981001 : ℝ) ≤ 0.679644485348 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602656981001 : ℝ)) (Q := (0.602656981001 : ℝ))
      (s := (0.798000352914 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775327560988 : ℝ)) (R := (0.775869886155 : ℝ)) (Q2 := (0.602656981001 : ℝ)) (T := (0.824872749382 : ℝ))
    (B := ((6816166555730509/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243154102217/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810573364813143/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599950854989 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486308204434 : ℝ)) (s := (0.873787348444 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601864947926 : ℝ) ≤ 0.679083492998 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601864947926 : ℝ)) (Q := (0.601864947926 : ℝ))
      (s := (0.798597886586 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774817555572 : ℝ)) (R := (0.775359880739 : ℝ)) (Q2 := (0.601864947926 : ℝ)) (T := (0.824532245750 : ℝ))
    (B := ((6810573364813143/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (242557526711/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804986339219417/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599160804569 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485115053422 : ℝ)) (s := (0.874450333035 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601073447448 : ℝ) ≤ 0.678523141690 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601073447448 : ℝ)) (Q := (0.601073447448 : ℝ))
      (s := (0.799193787997 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774307557759 : ℝ)) (R := (0.774849882926 : ℝ)) (Q2 := (0.601073447448 : ℝ)) (T := (0.824191990775 : ℝ))
    (B := ((6804986339219417/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483921902409/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1699851367349521/2500000000000000) := by
  have hk1 : kappa q ≤ 0.598371285578 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483921902409 : ℝ)) (s := (0.875111188575 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600282479009 : ℝ) ≤ 0.677963430268 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600282479009 : ℝ)) (Q := (0.600282479009 : ℝ))
      (s := (0.799788062799 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773797567204 : ℝ)) (R := (0.774339892371 : ℝ)) (Q2 := (0.600282479009 : ℝ)) (T := (0.823851984064 : ℝ))
    (B := ((1699851367349521/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482728751397/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793830745833061/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597582297464 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482728751397 : ℝ)) (s := (0.875769919885 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599492042058 : ℝ) ≤ 0.677404357579 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599492042058 : ℝ)) (Q := (0.599492042058 : ℝ))
      (s := (0.800380716603 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773287583566 : ℝ)) (R := (0.773829908733 : ℝ)) (Q2 := (0.599492042058 : ℝ)) (T := (0.823512225223 : ℝ))
    (B := ((6793830745833061/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1880998439/3906250000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (678826182144763/1000000000000000) := by
  have hk1 : kappa q ≤ 0.596793839677 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481535600384 : ℝ)) (s := (0.876426531755 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598702136043 : ℝ) ≤ 0.676845922475 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598702136043 : ℝ)) (Q := (0.598702136043 : ℝ))
      (s := (0.800971754994 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772777606502 : ℝ)) (R := (0.773319931669 : ℝ)) (Q2 := (0.598702136043 : ℝ)) (T := (0.823172713861 : ℝ))
    (B := ((678826182144763/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480342449371/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1695674548174579/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596005911672 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480342449371 : ℝ)) (s := (0.877081028944 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597912760415 : ℝ) ≤ 0.676288123810 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597912760415 : ℝ)) (Q := (0.597912760415 : ℝ))
      (s := (0.801561183525 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772267635671 : ℝ)) (R := (0.772809960838 : ℝ)) (Q2 := (0.597912760415 : ℝ)) (T := (0.822833449587 : ℝ))
    (B := ((1695674548174579/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479149298359/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777140684430123/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595218512906 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479149298359 : ℝ)) (s := (0.877733416182 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597123914636 : ℝ) ≤ 0.675730960449 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597123914636 : ℝ)) (Q := (0.597123914636 : ℝ))
      (s := (0.802149007710 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771757670736 : ℝ)) (R := (0.772299995903 : ℝ)) (Q2 := (0.597123914636 : ℝ)) (T := (0.822494432017 : ℝ))
    (B := ((6777140684430123/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12775 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (238978073673/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (211612165226871/312500000000000) := by
  have hk1 : kappa q ≤ 0.594431642837 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477956147346 : ℝ)) (s := (0.878383698172 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596335598158 : ℝ) ≤ 0.675174431250 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596335598158 : ℝ)) (Q := (0.596335598158 : ℝ))
      (s := (0.802735233044 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771247711355 : ℝ)) (R := (0.771790036522 : ℝ)) (Q2 := (0.596335598158 : ℝ)) (T := (0.822155660759 : ℝ))
    (B := ((211612165226871/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S17
namespace BstLean.Part269.S17
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12775 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052328354345 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S17.wn_upper (by omega : 12775 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010565992044 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035703027963)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010565992044 + 2 * 0.737676 / 12775) := by gcongr
    _ ≤ (0.052328354345 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12775 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12775 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.026545554573 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12775 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.026545554573 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12775 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003459522332 + 0.003273654356 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003459522332 + 0.003273654356 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.026545554573 ≤ R)
    (hB : (X + 0.052328354345 + R + 0.008456384432) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008456384432 := by
    convert (BstLean.Part269.S17.finite_centre_upper (by omega : 12775 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (21301670721/250000000000)
  | 2 => (17228867373/200000000000)
  | 3 => (21769851453/250000000000)
  | 4 => (88013139563/1000000000000)
  | 5 => (88947055197/1000000000000)
  | 6 => (89882977417/1000000000000)
  | 7 => (90823082851/1000000000000)
  | 8 => (45884974171/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003459522332 + 0.003273654356 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218928317349 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010934311693 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003459522332 + 0.003273654356 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220499798207 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011048941003 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003459522332 + 0.003273654356 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222050748433 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011163191702 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003459522332 + 0.003273654356 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223581377760 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011277072090 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003459522332 + 0.003273654356 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225091890630 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011390590229 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003459522332 + 0.003273654356 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226582484705 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011503753832 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003459522332 + 0.003273654356 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228053352754 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011616570403 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12775 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003459522332 + 0.003273654356 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229504681194 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011729047125 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12775 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g) :
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

end BstLean.Part269.S17

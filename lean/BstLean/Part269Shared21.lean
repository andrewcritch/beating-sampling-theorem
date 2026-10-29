import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S21
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12875 ≤ n) : wn n ≤ 1.035562891551 := by
  have hnR : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.468057179102 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.468057179102 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035562891551 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12875 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12875 + 24 / (12875 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12875 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008423339564 : ℝ) := by
  have hnR : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.468057179102 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12875 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035562891551 * (81 / 1000 / 12875)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035562891551 * n *
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
        4 * (1 / 2.506628) * 1.035562891551 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035562891551 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035562891551 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12875)) / 113.468057179102 := by gcongr
    _ ≤ (0.008423339564 : ℝ) := by norm_num

end BstLean.Part269.S21
namespace BstLean.Part269.S21
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12875 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12875 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12875 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12875 + 0.008423339564 / 113.468057179102) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12875 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12875 := by gcongr
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
  have hn : (113.468057179102 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S21.finite_centre_upper (by omega : 12875 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528079003107/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3504939425394733/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627949070892 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528079003107 : ℝ)) (s := (0.849195246382 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629904586249 : ℝ) ≤ 0.699106320019 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629904586249 : ℝ)) (Q := (0.629904586249 : ℝ))
      (s := (0.776672525730 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792677374729 : ℝ)) (R := (0.793215487662 : ℝ)) (Q2 := (0.629904586249 : ℝ)) (T := (0.836599637093 : ℝ))
    (B := ((3504939425394733/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263443451709/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004075359455003/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627140756181 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526886903418 : ℝ)) (s := (0.849935404020 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629094805029 : ℝ) ≤ 0.698523327961 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629094805029 : ℝ)) (Q := (0.629094805029 : ℝ))
      (s := (0.777328583217 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792167347027 : ℝ)) (R := (0.792705459960 : ℝ)) (Q2 := (0.629094805029 : ℝ)) (T := (0.836250739755 : ℝ))
    (B := ((7004075359455003/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525694803729/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998278369054631/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626332993215 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525694803729 : ℝ)) (s := (0.850673247101 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628285576202 : ℝ) ≤ 0.697941017591 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628285576202 : ℝ)) (Q := (0.628285576202 : ℝ))
      (s := (0.777982798484 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791657339213 : ℝ)) (R := (0.792195452146 : ℝ)) (Q2 := (0.628285576202 : ℝ)) (T := (0.835902105009 : ℝ))
    (B := ((6998278369054631/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524502704039/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1398497573747297/2000000000000000) := by
  have hk1 : kappa q ≤ 0.625525781334 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524502704039 : ℝ)) (s := (0.851408781642 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627476899106 : ℝ) ≤ 0.697359387614 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627476899106 : ℝ)) (Q := (0.627476899106 : ℝ))
      (s := (0.778635178430 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791147350908 : ℝ)) (R := (0.791685463841 : ℝ)) (Q2 := (0.627476899106 : ℝ)) (T := (0.835553732408 : ℝ))
    (B := ((1398497573747297/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (10466212087/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3493351923845871/5000000000000000) := by
  have hk1 : kappa q ≤ 0.624719119883 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523310604350 : ℝ)) (s := (0.852142013620 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668773085 : ℝ) ≤ 0.696778436740 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668773085 : ℝ)) (Q := (0.626668773085 : ℝ))
      (s := (0.779285729910 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790637381736 : ℝ)) (R := (0.791175494669 : ℝ)) (Q2 := (0.626668773085 : ℝ)) (T := (0.835205621507 : ℝ))
    (B := ((3493351923845871/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522118504661/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1396185259030871/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623913008209 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522118504661 : ℝ)) (s := (0.852872948974 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625861197485 : ℝ) ≤ 0.696198163679 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625861197485 : ℝ)) (Q := (0.625861197485 : ℝ))
      (s := (0.779934459736 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790127431320 : ℝ)) (R := (0.790665544253 : ℝ)) (Q2 := (0.625861197485 : ℝ)) (T := (0.834857771859 : ℝ))
    (B := ((1396185259030871/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520926404971/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975155200400779/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623107445661 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520926404971 : ℝ)) (s := (0.853601593605 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625054171655 : ℝ) ≤ 0.695618567149 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625054171655 : ℝ)) (Q := (0.625054171655 : ℝ))
      (s := (0.780581374680 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789617499285 : ℝ)) (R := (0.790155612218 : ℝ)) (Q2 := (0.625054171655 : ℝ)) (T := (0.834510183023 : ℝ))
    (B := ((6975155200400779/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259867152641/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (435586909546857/625000000000000) := by
  have hk1 : kappa q ≤ 0.622302431595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519734305282 : ℝ)) (s := (0.854327953373 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624247694946 : ℝ) ≤ 0.695039645870 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624247694946 : ℝ)) (Q := (0.624247694946 : ℝ))
      (s := (0.781226481473 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789107585257 : ℝ)) (R := (0.789645698190 : ℝ)) (Q2 := (0.624247694946 : ℝ)) (T := (0.834162854556 : ℝ))
    (B := ((435586909546857/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518542205593/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (278545293662473/400000000000000) := by
  have hk1 : kappa q ≤ 0.621497965366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518542205593 : ℝ)) (s := (0.855052034101 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623441766716 : ℝ) ≤ 0.694461398569 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623441766716 : ℝ)) (Q := (0.623441766716 : ℝ))
      (s := (0.781869786803 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788597688864 : ℝ)) (R := (0.789135801797 : ℝ)) (Q2 := (0.623441766716 : ℝ)) (T := (0.833815786019 : ℝ))
    (B := ((278545293662473/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517350105903/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1391576111247901/2000000000000000) := by
  have hk1 : kappa q ≤ 0.620694046333 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517350105903 : ℝ)) (s := (0.855773841574 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622636386321 : ℝ) ≤ 0.693883823973 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622636386321 : ℝ)) (Q := (0.622636386321 : ℝ))
      (s := (0.782511297318 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788087809732 : ℝ)) (R := (0.788625922665 : ℝ)) (Q2 := (0.622636386321 : ℝ)) (T := (0.833468976973 : ℝ))
    (B := ((1391576111247901/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258079003107/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952135186226597/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619890673859 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516158006214 : ℝ)) (s := (0.856493381540 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621831553123 : ℝ) ≤ 0.693306920814 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621831553123 : ℝ)) (Q := (0.621831553123 : ℝ))
      (s := (0.783151019626 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787577947491 : ℝ)) (R := (0.788116060424 : ℝ)) (Q2 := (0.621831553123 : ℝ)) (T := (0.833122426979 : ℝ))
    (B := ((6952135186226597/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20598636261/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389279244201629/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619087847309 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514965906525 : ℝ)) (s := (0.857210659708 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621027266486 : ℝ) ≤ 0.692730687830 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621027266486 : ℝ)) (Q := (0.621027266486 : ℝ))
      (s := (0.783788960296 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787068101770 : ℝ)) (R := (0.787606214703 : ℝ)) (Q2 := (0.621027266486 : ℝ)) (T := (0.832776135603 : ℝ))
    (B := ((1389279244201629/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102754761367/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940663650110139/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618285566053 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513773806835 : ℝ)) (s := (0.857925681753 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620223525780 : ℝ) ≤ 0.692155123763 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620223525780 : ℝ)) (Q := (0.620223525780 : ℝ))
      (s := (0.784425125853 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786558272201 : ℝ)) (R := (0.787096385134 : ℝ)) (Q2 := (0.620223525780 : ℝ)) (T := (0.832430102411 : ℝ))
    (B := ((6940663650110139/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256290853573/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6934937463099263/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617483829461 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512581707146 : ℝ)) (s := (0.858638453309 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619420330373 : ℝ) ≤ 0.691580227356 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619420330373 : ℝ)) (Q := (0.619420330373 : ℝ))
      (s := (0.785059522789 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786048458415 : ℝ)) (R := (0.786586571348 : ℝ)) (Q2 := (0.619420330373 : ℝ)) (T := (0.832084326969 : ℝ))
    (B := ((6934937463099263/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511389607457/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1385843529916529/2000000000000000) := by
  have hk1 : kappa q ≤ 0.616682636909 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511389607457 : ℝ)) (s := (0.859348979976 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618617679638 : ℝ) ≤ 0.691005997358 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618617679638 : ℝ)) (Q := (0.618617679638 : ℝ))
      (s := (0.785692157553 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785538660044 : ℝ)) (R := (0.786076772977 : ℝ)) (Q2 := (0.618617679638 : ℝ)) (T := (0.831738808845 : ℝ))
    (B := ((1385843529916529/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510197507767/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923504199207611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615881987774 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510197507767 : ℝ)) (s := (0.860057267320 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617815572954 : ℝ) ≤ 0.690432432524 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617815572954 : ℝ)) (Q := (0.617815572954 : ℝ))
      (s := (0.786323036555 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785028876723 : ℝ)) (R := (0.785566989656 : ℝ)) (Q2 := (0.617815572954 : ℝ)) (T := (0.831393547610 : ℝ))
    (B := ((6923504199207611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (254502704039/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1729449275415359/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615081881438 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509005408078 : ℝ)) (s := (0.860763320866 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617014009701 : ℝ) ≤ 0.689859531610 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617014009701 : ℝ)) (Q := (0.617014009701 : ℝ))
      (s := (0.786952166166 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784519108087 : ℝ)) (R := (0.785057221020 : ℝ)) (Q2 := (0.617014009701 : ℝ)) (T := (0.831048542836 : ℝ))
    (B := ((1729449275415359/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507813308389/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1382419269334221/2000000000000000) := by
  have hk1 : kappa q ≤ 0.614282317285 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507813308389 : ℝ)) (s := (0.861467146108 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616212989261 : ℝ) ≤ 0.689287293379 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616212989261 : ℝ)) (Q := (0.616212989261 : ℝ))
      (s := (0.787579552723 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784009353771 : ℝ)) (R := (0.784547466704 : ℝ)) (Q2 := (0.616212989261 : ℝ)) (T := (0.830703794097 : ℝ))
    (B := ((1382419269334221/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506621208699/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1726600481000767/2500000000000000) := by
  have hk1 : kappa q ≤ 0.613483294700 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506621208699 : ℝ)) (s := (0.862168748504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615412511018 : ℝ) ≤ 0.688715716594 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615412511018 : ℝ)) (Q := (0.615412511018 : ℝ))
      (s := (0.788205202522 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783499613411 : ℝ)) (R := (0.784037726344 : ℝ)) (Q2 := (0.615412511018 : ℝ)) (T := (0.830359300966 : ℝ))
    (B := ((1726600481000767/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50542910901/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900713823463003/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612684813077 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505429109010 : ℝ)) (s := (0.862868133475 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614612574367 : ℝ) ≤ 0.688144800029 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614612574367 : ℝ)) (Q := (0.614612574367 : ℝ))
      (s := (0.788829121820 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782989886648 : ℝ)) (R := (0.783527999581 : ℝ)) (Q2 := (0.614612574367 : ℝ)) (T := (0.830015063021 : ℝ))
    (B := ((6900713823463003/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504237009321/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (344751601744779/500000000000000) := by
  have hk1 : kappa q ≤ 0.611886871807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504237009321 : ℝ)) (s := (0.863565306408 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613813178694 : ℝ) ≤ 0.687574542454 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613813178694 : ℝ)) (Q := (0.613813178694 : ℝ))
      (s := (0.789451316841 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782480173118 : ℝ)) (R := (0.783018286051 : ℝ)) (Q2 := (0.613813178694 : ℝ)) (T := (0.829671079838 : ℝ))
    (B := ((344751601744779/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503044909631/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889356548184221/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611089470286 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503044909631 : ℝ)) (s := (0.864260272658 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613014323396 : ℝ) ≤ 0.687004942649 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613014323396 : ℝ)) (Q := (0.613014323396 : ℝ))
      (s := (0.790071793771 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781970472461 : ℝ)) (R := (0.782508585394 : ℝ)) (Q2 := (0.613014323396 : ℝ)) (T := (0.829327350998 : ℝ))
    (B := ((6889356548184221/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250926404971/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883687353250873/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610292607916 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501852809942 : ℝ)) (s := (0.864953037543 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612216007876 : ℝ) ≤ 0.686435999398 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612216007876 : ℝ)) (Q := (0.612216007876 : ℝ))
      (s := (0.790690558753 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781460784321 : ℝ)) (R := (0.781998897254 : ℝ)) (Q2 := (0.612216007876 : ℝ)) (T := (0.828983876083 : ℝ))
    (B := ((6883687353250873/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500660710253/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439012220027887/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609496284098 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500660710253 : ℝ)) (s := (0.865643606347 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611418231531 : ℝ) ≤ 0.685867711485 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611418231531 : ℝ)) (Q := (0.611418231531 : ℝ))
      (s := (0.791307617904 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780951108337 : ℝ)) (R := (0.781489221270 : ℝ)) (Q2 := (0.611418231531 : ℝ)) (T := (0.828640654675 : ℝ))
    (B := ((3439012220027887/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499468610563/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872367798597221/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608700498237 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499468610563 : ℝ)) (s := (0.866331984324 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610620993766 : ℝ) ≤ 0.685300077702 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610620993766 : ℝ)) (Q := (0.610620993766 : ℝ))
      (s := (0.791922977298 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780441444153 : ℝ)) (R := (0.780979557086 : ℝ)) (Q2 := (0.610620993766 : ℝ)) (T := (0.828297686357 : ℝ))
    (B := ((6872367798597221/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249138255437/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866717418911349/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607905249745 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498276510874 : ℝ)) (s := (0.867018176691 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609824293992 : ℝ) ≤ 0.684733096845 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609824293992 : ℝ)) (Q := (0.609824293992 : ℝ))
      (s := (0.792536642975 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779931791415 : ℝ)) (R := (0.780469904348 : ℝ)) (Q2 := (0.609824293992 : ℝ)) (T := (0.827954970718 : ℝ))
    (B := ((6866717418911349/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99416882237/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861073291071901/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607110538031 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497084411185 : ℝ)) (s := (0.867702188633 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609028131617 : ℝ) ≤ 0.684166767713 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609028131617 : ℝ)) (Q := (0.609028131617 : ℝ))
      (s := (0.793148620941 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779422149766 : ℝ)) (R := (0.779960262699 : ℝ)) (Q2 := (0.609028131617 : ℝ)) (T := (0.827612507344 : ℝ))
    (B := ((6861073291071901/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61986538937/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855435405190007/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606316362512 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495892311496 : ℝ)) (s := (0.868384025302 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608232506058 : ℝ) ≤ 0.683601089110 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608232506058 : ℝ)) (Q := (0.608232506058 : ℝ))
      (s := (0.793758917163 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778912518854 : ℝ)) (R := (0.779450631787 : ℝ)) (Q2 := (0.608232506058 : ℝ)) (T := (0.827270295825 : ℝ))
    (B := ((6855435405190007/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247350105903/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849803751413961/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605522722604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494700211806 : ℝ)) (s := (0.869063691820 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607437416727 : ℝ) ≤ 0.683036059840 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607437416727 : ℝ)) (Q := (0.607437416727 : ℝ))
      (s := (0.794367537580 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778402898324 : ℝ)) (R := (0.778941011257 : ℝ)) (Q2 := (0.607437416727 : ℝ)) (T := (0.826928335749 : ℝ))
    (B := ((6849803751413961/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493508112117/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422089159964501/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604729617731 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493508112117 : ℝ)) (s := (0.869741193273 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606642863050 : ℝ) ≤ 0.682471678720 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606642863050 : ℝ)) (Q := (0.606642863050 : ℝ))
      (s := (0.794974488088 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777893287827 : ℝ)) (R := (0.778431400760 : ℝ)) (Q2 := (0.606642863050 : ℝ)) (T := (0.826586626713 : ℝ))
    (B := ((3422089159964501/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123079003107/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (854819887619637/1250000000000000) := by
  have hk1 : kappa q ≤ 0.603937047316 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492316012428 : ℝ)) (s := (0.870416534716 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605848844447 : ℝ) ≤ 0.681907944564 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605848844447 : ℝ)) (Q := (0.605848844447 : ℝ))
      (s := (0.795579774556 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777383687011 : ℝ)) (R := (0.777921799944 : ℝ)) (Q2 := (0.605848844447 : ℝ)) (T := (0.826245168309 : ℝ))
    (B := ((854819887619637/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245561956369/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416473042378361/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603145010786 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491123912738 : ℝ)) (s := (0.871089721176 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605055360345 : ℝ) ≤ 0.681344856193 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605055360345 : ℝ)) (Q := (0.605055360345 : ℝ))
      (s := (0.796183402815 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776874095527 : ℝ)) (R := (0.777412208460 : ℝ)) (Q2 := (0.605055360345 : ℝ)) (T := (0.825903960134 : ℝ))
    (B := ((3416473042378361/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489931813049/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413669630811327/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602353507573 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489931813049 : ℝ)) (s := (0.871760757641 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604262410174 : ℝ) ≤ 0.680782412431 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604262410174 : ℝ)) (Q := (0.604262410174 : ℝ))
      (s := (0.796785378663 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776364513027 : ℝ)) (R := (0.776902625960 : ℝ)) (Q2 := (0.604262410174 : ℝ)) (T := (0.825563001784 : ℝ))
    (B := ((3413669630811327/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (6109246417/12500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852717327735719/1250000000000000) := by
  have hk1 : kappa q ≤ 0.601562537110 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488739713360 : ℝ)) (s := (0.872429649075 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603469993368 : ℝ) ≤ 0.680220612110 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603469993368 : ℝ)) (Q := (0.603469993368 : ℝ))
      (s := (0.797385707864 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775854939164 : ℝ)) (R := (0.776393052097 : ℝ)) (Q2 := (0.603469993368 : ℝ)) (T := (0.825222292862 : ℝ))
    (B := ((852717327735719/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48754761367/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27264576623651/40000000000000) := by
  have hk1 : kappa q ≤ 0.600772098833 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487547613670 : ℝ)) (s := (0.873096400408 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602678109361 : ℝ) ≤ 0.679659454059 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602678109361 : ℝ)) (Q := (0.602678109361 : ℝ))
      (s := (0.797984396149 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775345373591 : ℝ)) (R := (0.775883486524 : ℝ)) (Q2 := (0.602678109361 : ℝ)) (T := (0.824881832965 : ℝ))
    (B := ((27264576623651/40000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486355513981/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810555854106047/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599982192184 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486355513981 : ℝ)) (s := (0.873761016538 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601886757591 : ℝ) ≤ 0.679098937118 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601886757591 : ℝ)) (Q := (0.601886757591 : ℝ))
      (s := (0.798581449219 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774835815963 : ℝ)) (R := (0.775373928896 : ℝ)) (Q2 := (0.601886757591 : ℝ)) (T := (0.824541621698 : ℝ))
    (B := ((6810555854106047/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (121290853573/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804973706903499/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599192816604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485163414292 : ℝ)) (s := (0.874423502334 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601095937504 : ℝ) ≤ 0.678539060130 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601095937504 : ℝ)) (Q := (0.601095937504 : ℝ))
      (s := (0.799176872737 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774326265937 : ℝ)) (R := (0.774864378870 : ℝ)) (Q2 := (0.601095937504 : ℝ)) (T := (0.824201658665 : ℝ))
    (B := ((6804973706903499/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241985657301/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799397704778217/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598403971539 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483971314602 : ℝ)) (s := (0.875083862634 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600305648539 : ℝ) ≤ 0.677979821937 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600305648539 : ℝ)) (Q := (0.600305648539 : ℝ))
      (s := (0.799770672339 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773816723168 : ℝ)) (R := (0.774354836101 : ℝ)) (Q2 := (0.600305648539 : ℝ)) (T := (0.823861943471 : ℝ))
    (B := ((6799397704778217/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482779214913/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793827838238359/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597615656439 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482779214913 : ℝ)) (s := (0.875742102247 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599515890149 : ℝ) ≤ 0.677421221393 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599515890149 : ℝ)) (Q := (0.599515890149 : ℝ))
      (s := (0.800362853623 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773307187316 : ℝ)) (R := (0.773845300249 : ℝ)) (Q2 := (0.599515890149 : ℝ)) (T := (0.823522475726 : ℝ))
    (B := ((6793827838238359/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60198389403/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (135765271103271/200000000000000) := by
  have hk1 : kappa q ≤ 0.596827870756 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481587115224 : ℝ)) (s := (0.876398225952 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598726661782 : ℝ) ≤ 0.676863257351 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598726661782 : ℝ)) (Q := (0.598726661782 : ℝ))
      (s := (0.800953422161 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772797658039 : ℝ)) (R := (0.773335770972 : ℝ)) (Q2 := (0.598726661782 : ℝ)) (T := (0.823183255038 : ℝ))
    (B := ((135765271103271/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240197507767/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3391352388088957/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596040613943 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480395015534 : ℝ)) (s := (0.877052238496 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597937962894 : ℝ) ≤ 0.676305928670 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597937962894 : ℝ)) (Q := (0.597937962894 : ℝ))
      (s := (0.801542383490 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772288134998 : ℝ)) (R := (0.772826247931 : ℝ)) (Q2 := (0.597937962894 : ℝ)) (T := (0.822844281020 : ℝ))
    (B := ((3391352388088957/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (95840583169/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3388576053520903/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595253885462 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479202915845 : ℝ)) (s := (0.877704144599 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597149792942 : ℝ) ≤ 0.675749234213 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597149792942 : ℝ)) (Q := (0.597149792942 : ℝ))
      (s := (0.802129743115 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771778617854 : ℝ)) (R := (0.772316730787 : ℝ)) (Q2 := (0.597149792942 : ℝ)) (T := (0.822505553283 : ℝ))
    (B := ((3388576053520903/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12875 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (119502704039/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771605538395899/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594467684772 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478010816156 : ℝ)) (s := (0.878353948952 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596362151388 : ℝ) ≤ 0.675193172849 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596362151388 : ℝ)) (Q := (0.596362151388 : ℝ))
      (s := (0.802715506511 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771269106271 : ℝ)) (R := (0.771807219204 : ℝ)) (Q2 := (0.596362151388 : ℝ)) (T := (0.822167071443 : ℝ))
    (B := ((6771605538395899/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S21
namespace BstLean.Part269.S21
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12875 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052122548417 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S21.wn_upper (by omega : 12875 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010524879079 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035562891551)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010524879079 + 2 * 0.737676 / 12875) := by gcongr
    _ ≤ (0.052122548417 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12875 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12875 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.468057179102 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12875 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.468057179102 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12875 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003338665865 + 0.003247348463 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003338665865 + 0.003247348463 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.468057179102 ≤ R)
    (hB : (X + 0.052122548417 + R + 0.008423339564) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008423339564 := by
    convert (BstLean.Part269.S21.finite_centre_upper (by omega : 12875 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (84930022003/1000000000000)
  | 2 => (42931459551/500000000000)
  | 3 => (86792590893/1000000000000)
  | 4 => (87720136183/1000000000000)
  | 5 => (88646893759/1000000000000)
  | 6 => (17914895851/200000000000)
  | 7 => (707068951/7812500000)
  | 8 => (45720114001/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003338665865 + 0.003247348463 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218623585947 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010891765571 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003338665865 + 0.003247348463 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220196811716 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011005948852 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003338665865 + 0.003247348463 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221749454220 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011119754994 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003338665865 + 0.003247348463 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223281725035 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011233192265 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003338665865 + 0.003247348463 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224793830358 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011346268698 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003338665865 + 0.003247348463 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226285969518 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011458991974 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003338665865 + 0.003247348463 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227758336871 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011571369569 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12875 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003338665865 + 0.003247348463 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229211120342 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011683408636 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12875 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g) :
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

end BstLean.Part269.S21

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S19
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12825 ≤ n) : wn n ≤ 1.035632753694 := by
  have hnR : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.247516529061 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.247516529061 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035632753694 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12825 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12825 + 24 / (12825 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12825 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008439813548 : ℝ) := by
  have hnR : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.247516529061 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12825 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035632753694 * (81 / 1000 / 12825)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035632753694 * n *
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
        4 * (1 / 2.506628) * 1.035632753694 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035632753694 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035632753694 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12825)) / 113.247516529061 := by gcongr
    _ ≤ (0.008439813548 : ℝ) := by norm_num

end BstLean.Part269.S19
namespace BstLean.Part269.S19
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12825 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12825 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12825 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12825 + 0.008439813548 / 113.247516529061) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12825 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12825 := by gcongr
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
  have hn : (113.247516529061 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S19.finite_centre_upper (by omega : 12825 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16502305067/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7009976041795279/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627945515998 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528073762144 : ℝ)) (s := (0.849198505496 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629905873644 : ℝ) ≤ 0.699107247090 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629905873644 : ℝ)) (Q := (0.629905873644 : ℝ))
      (s := (0.776671481612 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792676087407 : ℝ)) (R := (0.793216298246 : ℝ)) (Q2 := (0.629905873644 : ℝ)) (T := (0.836600191791 : ℝ))
    (B := ((7009976041795279/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526881138359/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004169923950789/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627136848469 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526881138359 : ℝ)) (s := (0.849938977835 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629095736822 : ℝ) ≤ 0.698523998630 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629095736822 : ℝ)) (Q := (0.629095736822 : ℝ))
      (s := (0.777327829113 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792165836184 : ℝ)) (R := (0.792706047023 : ℝ)) (Q2 := (0.629095736822 : ℝ)) (T := (0.836251141207 : ℝ))
    (B := ((7004169923950789/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525688514573/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1749592578208487/2500000000000000) := by
  have hk1 : kappa q ≤ 0.626328733165 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525688514573 : ℝ)) (s := (0.850677133610 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628286152874 : ℝ) ≤ 0.697941432456 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628286152874 : ℝ)) (Q := (0.628286152874 : ℝ))
      (s := (0.777982332773 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791655604865 : ℝ)) (R := (0.792195815704 : ℝ)) (Q2 := (0.628286152874 : ℝ)) (T := (0.835902353445 : ℝ))
    (B := ((1749592578208487/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131123972697/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496288598789233/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625521169428 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524495890788 : ℝ)) (s := (0.851412978846 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477121137 : ℝ) ≤ 0.697359547269 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477121137 : ℝ)) (Q := (0.627477121137 : ℝ))
      (s := (0.778634999503 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791145393070 : ℝ)) (R := (0.791685603909 : ℝ)) (Q2 := (0.627477121137 : ℝ)) (T := (0.835553828055 : ℝ))
    (B := ((3496288598789233/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261651633501/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (873348820920147/1250000000000000) := by
  have hk1 : kappa q ≤ 0.624714156601 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523303267002 : ℝ)) (s := (0.852146519529 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668640958 : ℝ) ≤ 0.696778341778 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668640958 : ℝ)) (Q := (0.626668640958 : ℝ))
      (s := (0.779285836161 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790635200424 : ℝ)) (R := (0.791175411263 : ℝ)) (Q2 := (0.626668640958 : ℝ)) (T := (0.835205564593 : ℝ))
    (B := ((873348820920147/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32631915201/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981010411401757/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623907694031 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522110643216 : ℝ)) (s := (0.852877761606 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625860711680 : ℝ) ≤ 0.696197814695 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625860711680 : ℝ)) (Q := (0.625860711680 : ℝ))
      (s := (0.779934849572 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790125026549 : ℝ)) (R := (0.790665237388 : ℝ)) (Q2 := (0.625860711680 : ℝ)) (T := (0.834857562614 : ℝ))
    (B := ((6981010411401757/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520918019431/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975236718962469/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623101781068 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520918019431 : ℝ)) (s := (0.853606710982 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625053332653 : ℝ) ≤ 0.695617964734 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625053332653 : ℝ)) (Q := (0.625053332653 : ℝ))
      (s := (0.780582046514 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789614871071 : ℝ)) (R := (0.790155081910 : ℝ)) (Q2 := (0.625053332653 : ℝ)) (T := (0.834509821674 : ℝ))
    (B := ((6975236718962469/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103945079129/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1393893895869577/2000000000000000) := by
  have hk1 : kappa q ≤ 0.622296417062 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519725395645 : ℝ)) (s := (0.854333373527 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624246503224 : ℝ) ≤ 0.695038790612 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624246503224 : ℝ)) (Q := (0.624246503224 : ℝ))
      (s := (0.781227433731 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789104733613 : ℝ)) (R := (0.789644944452 : ℝ)) (Q2 := (0.624246503224 : ℝ)) (T := (0.834162341330 : ℝ))
    (B := ((1393893895869577/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25926638593/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1740927170476157/2500000000000000) := by
  have hk1 : kappa q ≤ 0.621491601371 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518532771860 : ℝ)) (s := (0.855057755072 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623440222752 : ℝ) ≤ 0.694460291056 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623440222752 : ℝ)) (Q := (0.623440222752 : ℝ))
      (s := (0.781871017915 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788594613803 : ℝ)) (R := (0.789134824642 : ℝ)) (Q2 := (0.623440222752 : ℝ)) (T := (0.833815121142 : ℝ))
    (B := ((1740927170476157/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258670074037/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6957954316021111/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620687333351 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517340148074 : ℝ)) (s := (0.855779861408 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622634490590 : ℝ) ≤ 0.693882464788 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622634490590 : ℝ)) (Q := (0.622634490590 : ℝ))
      (s := (0.782512805728 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788084511267 : ℝ)) (R := (0.788624722106 : ℝ)) (Q2 := (0.622634490590 : ℝ)) (T := (0.833468160669 : ℝ))
    (B := ((6957954316021111/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (8064805067/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3476103185563637/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619883612366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516147524288 : ℝ)) (s := (0.856499698291 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621829306103 : ℝ) ≤ 0.693305310544 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621829306103 : ℝ)) (Q := (0.621829306103 : ℝ))
      (s := (0.783152803782 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787574425635 : ℝ)) (R := (0.788114636474 : ℝ)) (Q2 := (0.621829306103 : ℝ)) (T := (0.833121459476 : ℝ))
    (B := ((3476103185563637/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514954900503/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (694646483669433/1000000000000000) := by
  have hk1 : kappa q ≤ 0.619080437781 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514954900503 : ℝ)) (s := (0.857217271436 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621024668654 : ℝ) ≤ 0.692728827058 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621024668654 : ℝ)) (Q := (0.621024668654 : ℝ))
      (s := (0.783791018655 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787064356536 : ℝ)) (R := (0.787604567375 : ℝ)) (Q2 := (0.621024668654 : ℝ)) (T := (0.832775017125 : ℝ))
    (B := ((694646483669433/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513762276717/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940729702234509/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618277808961 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513762276717 : ℝ)) (s := (0.857932586526 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620220577606 : ℝ) ≤ 0.692153013067 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620220577606 : ℝ)) (Q := (0.620220577606 : ℝ))
      (s := (0.784427456885 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786554303599 : ℝ)) (R := (0.787094514438 : ℝ)) (Q2 := (0.620220577606 : ℝ)) (T := (0.832428833181 : ℝ))
    (B := ((6940729702234509/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512569652931/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935000957300807/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617475725280 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512569652931 : ℝ)) (s := (0.858645649203 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619417032332 : ℝ) ≤ 0.691577867316 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619417032332 : ℝ)) (Q := (0.619417032332 : ℝ))
      (s := (0.785062124967 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786044266456 : ℝ)) (R := (0.786584477295 : ℝ)) (Q2 := (0.619417032332 : ℝ)) (T := (0.832082907210 : ℝ))
    (B := ((6935000957300807/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255688514573/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929278591486733/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616674186111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511377029146 : ℝ)) (s := (0.859356465073 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618614032205 : ℝ) ≤ 0.691003388553 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618614032205 : ℝ)) (Q := (0.618614032205 : ℝ))
      (s := (0.785695029359 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785534244740 : ℝ)) (R := (0.786074455579 : ℝ)) (Q2 := (0.618614032205 : ℝ)) (T := (0.831737238781 : ℝ))
    (B := ((6929278591486733/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (6377305067/12500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (432722662151629/625000000000000) := by
  have hk1 : kappa q ≤ 0.615873190830 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510184405360 : ℝ)) (s := (0.860065039708 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617811576599 : ℝ) ≤ 0.690429575528 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617811576599 : ℝ)) (Q := (0.617811576599 : ℝ))
      (s := (0.786326176482 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785024238083 : ℝ)) (R := (0.785564448922 : ℝ)) (Q2 := (0.617811576599 : ℝ)) (T := (0.831391827463 : ℝ))
    (B := ((432722662151629/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20359671263/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6917852955792597/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615072738818 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508991781575 : ℝ)) (s := (0.860771378642 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617009664895 : ℝ) ≤ 0.689856426999 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617009664895 : ℝ)) (Q := (0.617009664895 : ℝ))
      (s := (0.786955572715 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784514246121 : ℝ)) (R := (0.785054456960 : ℝ)) (Q2 := (0.617009664895 : ℝ)) (T := (0.831046672829 : ℝ))
    (B := ((6917852955792597/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507799157789/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (108002338520311/156250000000000) := by
  have hk1 : kappa q ≤ 0.614272829459 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507799157789 : ℝ)) (s := (0.861475487376 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616208296474 : ℝ) ≤ 0.689283941724 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616208296474 : ℝ)) (Q := (0.616208296474 : ℝ))
      (s := (0.787583224401 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784004268488 : ℝ)) (R := (0.784544479327 : ℝ)) (Q2 := (0.616208296474 : ℝ)) (T := (0.830701774449 : ℝ))
    (B := ((108002338520311/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506606534003/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3453226356350547/5000000000000000) := by
  have hk1 : kappa q ≤ 0.613473462138 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506606534003 : ℝ)) (s := (0.862177371372 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615407470722 : ℝ) ≤ 0.688712118468 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615407470722 : ℝ)) (Q := (0.615407470722 : ℝ))
      (s := (0.788209137844 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783494304821 : ℝ)) (R := (0.784034515660 : ℝ)) (Q2 := (0.615407470722 : ℝ)) (T := (0.830357131898 : ℝ))
    (B := ((3453226356350547/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252706955109/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1725190521947143/2500000000000000) := by
  have hk1 : kappa q ≤ 0.612674636247 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505413910218 : ℝ)) (s := (0.862877036060 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614607187028 : ℝ) ≤ 0.688140956000 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614607187028 : ℝ)) (Q := (0.614607187028 : ℝ))
      (s := (0.788833319310 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782984354758 : ℝ)) (R := (0.783524565597 : ℝ)) (Q2 := (0.614607187028 : ℝ)) (T := (0.830012744754 : ℝ))
    (B := ((1725190521947143/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15756915201/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895077780393797/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611876351176 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504221286432 : ℝ)) (s := (0.863574486833 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613807444782 : ℝ) ≤ 0.687570453091 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613807444782 : ℝ)) (Q := (0.613807444782 : ℝ))
      (s := (0.789455775032 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782474417936 : ℝ)) (R := (0.783014628775 : ℝ)) (Q2 := (0.613807444782 : ℝ)) (T := (0.829668612592 : ℝ))
    (B := ((6895077780393797/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503028662647/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444699890193527/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611078606322 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503028662647 : ℝ)) (s := (0.864269729052 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613008243380 : ℝ) ≤ 0.687000608519 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613008243380 : ℝ)) (Q := (0.613008243380 : ℝ))
      (s := (0.790076511199 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781964493996 : ℝ)) (R := (0.782504704835 : ℝ)) (Q2 := (0.613008243380 : ℝ)) (T := (0.829324734992 : ℝ))
    (B := ((3444699890193527/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501836038861/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883728077677213/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610281401083 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501836038861 : ℝ)) (s := (0.864962768043 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612209582220 : ℝ) ≤ 0.686431421064 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612209582220 : ℝ)) (Q := (0.612209582220 : ℝ))
      (s := (0.790695533969 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781454582578 : ℝ)) (R := (0.781994793417 : ℝ)) (Q2 := (0.612209582220 : ℝ)) (T := (0.828981111535 : ℝ))
    (B := ((6883728077677213/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20025736603/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439031331105751/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609484734862 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500643415075 : ℝ)) (s := (0.865653609097 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611411460701 : ℝ) ≤ 0.685862889512 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611411460701 : ℝ)) (Q := (0.611411460701 : ℝ))
      (s := (0.791312849462 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780944683323 : ℝ)) (R := (0.781484894162 : ℝ)) (Q2 := (0.611411460701 : ℝ)) (T := (0.828637741803 : ℝ))
    (B := ((3439031331105751/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49945079129/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872403523975279/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608688607064 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499450791290 : ℝ)) (s := (0.866342257471 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610613878229 : ℝ) ≤ 0.685295012652 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610613878229 : ℝ)) (Q := (0.610613878229 : ℝ))
      (s := (0.791928463761 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780434795875 : ℝ)) (R := (0.780975006714 : ℝ)) (Q2 := (0.610613878229 : ℝ)) (T := (0.828294625379 : ℝ))
    (B := ((6872403523975279/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31141135469/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866750652991797/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607893017096 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498258167504 : ℝ)) (s := (0.867028718392 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609816834210 : ℝ) ≤ 0.684727789277 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609816834210 : ℝ)) (Q := (0.609816834210 : ℝ))
      (s := (0.792542382914 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779924919877 : ℝ)) (R := (0.780465130716 : ℝ)) (Q2 := (0.609816834210 : ℝ)) (T := (0.827951761850 : ℝ))
    (B := ((6866750652991797/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497065543719/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1372220807864397/2000000000000000) := by
  have hk1 : kappa q ≤ 0.607097964371 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497065543719 : ℝ)) (s := (0.867712997049 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609020328055 : ℝ) ≤ 0.684161218186 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609020328055 : ℝ)) (Q := (0.609020328055 : ℝ))
      (s := (0.793154612933 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779415054974 : ℝ)) (R := (0.779955265813 : ℝ)) (Q2 := (0.609020328055 : ℝ)) (T := (0.827609150803 : ℝ))
    (B := ((1372220807864397/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495872919933/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855463673064223/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606303448302 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495872919933 : ℝ)) (s := (0.868395098603 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608224359175 : ℝ) ≤ 0.683595298179 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608224359175 : ℝ)) (Q := (0.608224359175 : ℝ))
      (s := (0.793765159797 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778905200811 : ℝ)) (R := (0.779445411650 : ℝ)) (Q2 := (0.608224359175 : ℝ)) (T := (0.827266791825 : ℝ))
    (B := ((6855463673064223/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494680296147/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849829544354117/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605509468307 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494680296147 : ℝ)) (s := (0.869075028179 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607428926990 : ℝ) ≤ 0.683030028064 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607428926990 : ℝ)) (Q := (0.607428926990 : ℝ))
      (s := (0.794374029445 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778395357036 : ℝ)) (R := (0.778935567875 : ℝ)) (Q2 := (0.607428926990 : ℝ)) (T := (0.826924684509 : ℝ))
    (B := ((6849829544354117/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246743836181/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422100821682141/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604716023808 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493487672362 : ℝ)) (s := (0.869752790871 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606634030919 : ℝ) ≤ 0.682465406652 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606634030919 : ℝ)) (Q := (0.606634030919 : ℝ))
      (s := (0.794981227786 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777885523298 : ℝ)) (R := (0.778425734137 : ℝ)) (Q2 := (0.606634030919 : ℝ)) (T := (0.826582828446 : ℝ))
    (B := ((3422100821682141/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (3846055067/7812500000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419289980152061/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603923114226 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492295048576 : ℝ)) (s := (0.870428391741 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605839670383 : ℝ) ≤ 0.681901432757 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605839670383 : ℝ)) (Q := (0.605839670383 : ℝ))
      (s := (0.795586760694 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777375699244 : ℝ)) (R := (0.777915910083 : ℝ)) (Q2 := (0.605839670383 : ℝ)) (T := (0.826241223230 : ℝ))
    (B := ((3419289980152061/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491102424791/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (213530140169363/312500000000000) := by
  have hk1 : kappa q ≤ 0.603130738990 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491102424791 : ℝ)) (s := (0.871101835818 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605045844809 : ℝ) ≤ 0.681338105199 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605045844809 : ℝ)) (Q := (0.605045844809 : ℝ))
      (s := (0.796190634007 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776865884525 : ℝ)) (R := (0.777406095364 : ℝ)) (Q2 := (0.605045844809 : ℝ)) (T := (0.825899868457 : ℝ))
    (B := ((213530140169363/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97981960201/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413677604496549/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602338897529 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489909801005 : ℝ)) (s := (0.871773128102 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604252553624 : ℝ) ≤ 0.680775422799 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604252553624 : ℝ)) (Q := (0.604252553624 : ℝ))
      (s := (0.796792853532 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776356078792 : ℝ)) (R := (0.776896289631 : ℝ)) (Q2 := (0.604252553624 : ℝ)) (T := (0.825558763722 : ℝ))
    (B := ((3413677604496549/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488717177219/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821752121343053/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601547589275 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488717177219 : ℝ)) (s := (0.872442273559 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603459796261 : ℝ) ≤ 0.680213384385 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603459796261 : ℝ)) (Q := (0.603459796261 : ℝ))
      (s := (0.797393425040 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775846281697 : ℝ)) (R := (0.776386492536 : ℝ)) (Q2 := (0.603459796261 : ℝ)) (T := (0.825217908626 : ℝ))
    (B := ((6821752121343053/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243762276717/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852019401602987/1250000000000000) := by
  have hk1 : kappa q ≤ 0.600756813667 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487524553434 : ℝ)) (s := (0.873109277124 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602667572159 : ℝ) ≤ 0.679651988793 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602667572159 : ℝ)) (Q := (0.602667572159 : ℝ))
      (s := (0.797992354267 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775336492896 : ℝ)) (R := (0.775876703735 : ℝ)) (Q2 := (0.602667572159 : ℝ)) (T := (0.824877302770 : ℝ))
    (B := ((852019401602987/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30395745603/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (681056447382577/1000000000000000) := by
  have hk1 : kappa q ≤ 0.599966570141 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486331929648 : ℝ)) (s := (0.873774143704 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601875880748 : ℝ) ≤ 0.679091234853 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601875880748 : ℝ)) (Q := (0.601875880748 : ℝ))
      (s := (0.798589646924 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774826712039 : ℝ)) (R := (0.775366922878 : ℝ)) (Q2 := (0.601875880748 : ℝ)) (T := (0.824536945754 : ℝ))
    (B := ((681056447382577/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (242569652931/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1360995978954867/2000000000000000) := by
  have hk1 : kappa q ≤ 0.599176858141 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485139305862 : ℝ)) (s := (0.874436878173 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601084721476 : ℝ) ≤ 0.678531121409 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601084721476 : ℝ)) (Q := (0.601084721476 : ℝ))
      (s := (0.799185308679 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774316938785 : ℝ)) (R := (0.774857149624 : ℝ)) (Q2 := (0.601084721476 : ℝ)) (T := (0.824196837184 : ℝ))
    (B := ((1360995978954867/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483946682077/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799401466130563/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598387677112 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483946682077 : ℝ)) (s := (0.875097485374 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600294093786 : ℝ) ≤ 0.677971647307 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600294093786 : ℝ)) (Q := (0.600294093786 : ℝ))
      (s := (0.799779345174 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773807172790 : ℝ)) (R := (0.774347383629 : ℝ)) (Q2 := (0.600294093786 : ℝ)) (T := (0.823856976667 : ℝ))
    (B := ((6799401466130563/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482754058291/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3396914589195267/5000000000000000) := by
  have hk1 : kappa q ≤ 0.597599026502 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482754058291 : ℝ)) (s := (0.875755970122 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599503997122 : ℝ) ≤ 0.677412811391 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599503997122 : ℝ)) (Q := (0.599503997122 : ℝ))
      (s := (0.800371762018 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773297413710 : ℝ)) (R := (0.773837624549 : ℝ)) (Q2 := (0.599503997122 : ℝ)) (T := (0.823517363805 : ℝ))
    (B := ((3396914589195267/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240780717253/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788262581047753/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596810905763 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481561434506 : ℝ)) (s := (0.876412337201 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598714430940 : ℝ) ≤ 0.676854612519 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598714430940 : ℝ)) (Q := (0.598714430940 : ℝ))
      (s := (0.800962564784 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772787661206 : ℝ)) (R := (0.773327872045 : ℝ)) (Q2 := (0.598714430940 : ℝ)) (T := (0.823177998213 : ℝ))
    (B := ((6788262581047753/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (3002305067/6250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782701384493563/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596023314349 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480368810720 : ℝ)) (s := (0.877066591365 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597925394688 : ℝ) ≤ 0.676297049544 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597925394688 : ℝ)) (Q := (0.597925394688 : ℝ))
      (s := (0.801551759020 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772277914936 : ℝ)) (R := (0.772818125775 : ℝ)) (Q2 := (0.597925394688 : ℝ)) (T := (0.822838879498 : ℝ))
    (B := ((6782701384493563/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (239588093467/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (677714630308761/1000000000000000) := by
  have hk1 : kappa q ≤ 0.595236251717 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479176186934 : ℝ)) (s := (0.877718737339 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597136887824 : ℝ) ≤ 0.675740121329 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597136887824 : ℝ)) (Q := (0.597136887824 : ℝ))
      (s := (0.802139350238 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771768174561 : ℝ)) (R := (0.772308385400 : ℝ)) (Q2 := (0.597136887824 : ℝ)) (T := (0.822500007273 : ℝ))
    (B := ((677714630308761/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12825 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477983563149/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385798663729341/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594449717330 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477983563149 : ℝ)) (s := (0.878368779819 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596348909811 : ℝ) ≤ 0.675183826743 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596348909811 : ℝ)) (Q := (0.596348909811 : ℝ))
      (s := (0.802725343918 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771258439745 : ℝ)) (R := (0.771798650584 : ℝ)) (Q2 := (0.596348909811 : ℝ)) (T := (0.822161381155 : ℝ))
    (B := ((3385798663729341/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S19
namespace BstLean.Part269.S19
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12825 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052225148355 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S19.wn_upper (by omega : 12825 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010545375455 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035632753694)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010545375455 + 2 * 0.737676 / 12825) := by gcongr
    _ ≤ (0.052225148355 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12825 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12825 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.247516529061 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12825 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.247516529061 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12825 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003397088065 + 0.003260455022 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003397088065 + 0.003260455022 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.247516529061 ≤ R)
    (hB : (X + 0.052225148355 + R + 0.008439813548) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008439813548 := by
    convert (BstLean.Part269.S19.finite_centre_upper (by omega : 12825 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (8506718329/100000000000)
  | 2 => (86002412933/1000000000000)
  | 3 => (5433420413/62500000000)
  | 4 => (87865296397/1000000000000)
  | 5 => (88795547641/1000000000000)
  | 6 => (22431799381/250000000000)
  | 7 => (45331148741/500000000000)
  | 8 => (91603279481/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003397088065 + 0.003260455022 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218771369689 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010912976430 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003397088065 + 0.003260455022 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220343754339 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011027382073 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003397088065 + 0.003260455022 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221895581200 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011141409844 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003397088065 + 0.003260455022 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223427060955 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011255068026 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003397088065 + 0.003260455022 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224938398950 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011368364665 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003397088065 + 0.003260455022 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226429793710 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011481307461 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003397088065 + 0.003260455022 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227901438819 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011593903903 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12825 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003397088065 + 0.003260455022 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229353521475 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011706161157 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12825 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g) :
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

end BstLean.Part269.S19

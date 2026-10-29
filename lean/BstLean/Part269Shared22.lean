import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S22
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12900 ≤ n) : wn n ≤ 1.035528113773 := by
  have hnR : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.578166916005 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.578166916005 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035528113773 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12900 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12900 + 24 / (12900 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12900 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008415138615 : ℝ) := by
  have hnR : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.578166916005 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12900 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035528113773 * (81 / 1000 / 12900)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035528113773 * n *
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
        4 * (1 / 2.506628) * 1.035528113773 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035528113773 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035528113773 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12900)) / 113.578166916005 := by gcongr
    _ ≤ (0.008415138615 : ℝ) := by norm_num

end BstLean.Part269.S22
namespace BstLean.Part269.S22
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12900 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12900 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12900 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12900 + 0.008415138615 / 113.578166916005) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12900 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12900 := by gcongr
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
  have hn : (113.578166916005 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S22.finite_centre_upper (by omega : 12900 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105616322389/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (109528602425103/156250000000000) := by
  have hk1 : kappa q ≤ 0.627950840446 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528081611945 : ℝ)) (s := (0.849193624050 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629903948738 : ℝ) ≤ 0.699105860939 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629903948738 : ℝ)) (Q := (0.629903948738 : ℝ))
      (s := (0.776673042770 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792678016187 : ℝ)) (R := (0.793215086265 : ℝ)) (Q2 := (0.629903948738 : ℝ)) (T := (0.836599362409 : ℝ))
    (B := ((109528602425103/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526889773139/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004028371195401/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627142701360 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526889773139 : ℝ)) (s := (0.849933625033 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629094344527 : ℝ) ≤ 0.698522996509 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629094344527 : ℝ)) (Q := (0.629094344527 : ℝ))
      (s := (0.777328955903 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792168099749 : ℝ)) (R := (0.792705169827 : ℝ)) (Q2 := (0.629094344527 : ℝ)) (T := (0.836250541353 : ℝ))
    (B := ((7004028371195401/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262848967167/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1749558171308867/2500000000000000) := by
  have hk1 : kappa q ≤ 0.626335113781 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525697934334 : ℝ)) (s := (0.850671312457 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628285292471 : ℝ) ≤ 0.697940813472 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628285292471 : ℝ)) (Q := (0.628285292471 : ℝ))
      (s := (0.777983027620 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791658203192 : ℝ)) (R := (0.792195273270 : ℝ)) (Q2 := (0.628285292471 : ℝ)) (T := (0.835901982776 : ℝ))
    (B := ((1749558171308867/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65563261941/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496221743241051/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625528077047 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524506095528 : ℝ)) (s := (0.851406692336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627476791906 : ℝ) ≤ 0.697359310531 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627476791906 : ℝ)) (Q := (0.627476791906 : ℝ))
      (s := (0.778635264819 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791148326136 : ℝ)) (R := (0.791685396214 : ℝ)) (Q2 := (0.627476791906 : ℝ)) (T := (0.835553686229 : ℝ))
    (B := ((3496221743241051/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523314256723/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986660764133619/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624721590504 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523314256723 : ℝ)) (s := (0.852139770643 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668842175 : ℝ) ≤ 0.696778486395 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668842175 : ℝ)) (Q := (0.626668842175 : ℝ))
      (s := (0.779285674350 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790638468204 : ℝ)) (R := (0.791175538282 : ℝ)) (Q2 := (0.626668842175 : ℝ)) (T := (0.835205651267 : ℝ))
    (B := ((6986660764133619/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522122417917/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6980884507431069/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623915653499 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522122417917 : ℝ)) (s := (0.852870553314 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625861442626 : ℝ) ≤ 0.696198339779 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625861442626 : ℝ)) (Q := (0.625861442626 : ℝ))
      (s := (0.779934263021 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790128629021 : ℝ)) (R := (0.790665699099 : ℝ)) (Q2 := (0.625861442626 : ℝ)) (T := (0.834857877446 : ℝ))
    (B := ((6980884507431069/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520930579111/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (697511470565797/1000000000000000) := by
  have hk1 : kappa q ≤ 0.623110265383 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520930579111 : ℝ)) (s := (0.853599046244 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625054592610 : ℝ) ≤ 0.695618869401 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625054592610 : ℝ)) (Q := (0.625054592610 : ℝ))
      (s := (0.780581037598 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789618808213 : ℝ)) (R := (0.790155878291 : ℝ)) (Q2 := (0.625054592610 : ℝ)) (T := (0.834510364324 : ℝ))
    (B := ((697511470565797/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259869370153/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1393870269628009/2000000000000000) := by
  have hk1 : kappa q ≤ 0.622305425511 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519738740306 : ℝ)) (s := (0.854325255290 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624248291478 : ℝ) ≤ 0.695040073982 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624248291478 : ℝ)) (Q := (0.624248291478 : ℝ))
      (s := (0.781226004808 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789109005405 : ℝ)) (R := (0.789646075483 : ℝ)) (Q2 := (0.624248291478 : ℝ)) (T := (0.834163111458 : ℝ))
    (B := ((1393870269628009/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1037093803/2000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6963594424244953/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621501133238 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518546901500 : ℝ)) (s := (0.855049186273 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623442538585 : ℝ) ≤ 0.694461952246 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623442538585 : ℝ)) (Q := (0.623442538585 : ℝ))
      (s := (0.781869171335 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788599220224 : ℝ)) (R := (0.789136290302 : ℝ)) (Q2 := (0.623442538585 : ℝ)) (T := (0.833816118409 : ℝ))
    (B := ((6963594424244953/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103471012539/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3478921961691017/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620697387924 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517355062695 : ℝ)) (s := (0.855770844972 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622637333290 : ℝ) ≤ 0.693884502923 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622637333290 : ℝ)) (Q := (0.622637333290 : ℝ))
      (s := (0.782510543823 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788089452298 : ℝ)) (R := (0.788626522376 : ℝ)) (Q2 := (0.622637333290 : ℝ)) (T := (0.833469384738 : ℝ))
    (B := ((3478921961691017/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516163223889/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (108626559921907/156250000000000) := by
  have hk1 : kappa q ≤ 0.619894188932 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516163223889 : ℝ)) (s := (0.856490237134 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621832674956 : ℝ) ≤ 0.693307724748 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621832674956 : ℝ)) (Q := (0.621832674956 : ℝ))
      (s := (0.783150128876 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787579701257 : ℝ)) (R := (0.788116771335 : ℝ)) (Q2 := (0.621832674956 : ℝ)) (T := (0.833122910008 : ℝ))
    (B := ((108626559921907/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128742846271/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (173659053714923/250000000000000) := by
  have hk1 : kappa q ≤ 0.619091535630 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514971385084 : ℝ)) (s := (0.857207368462 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621028562948 : ℝ) ≤ 0.692731616459 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621028562948 : ℝ)) (Q := (0.621028562948 : ℝ))
      (s := (0.783787933056 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787069966731 : ℝ)) (R := (0.787607036809 : ℝ)) (Q2 := (0.621028562948 : ℝ)) (T := (0.832776693785 : ℝ))
    (B := ((173659053714923/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256889773139/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940630853699483/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618289427384 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513779546278 : ℝ)) (s := (0.857922244628 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620224996632 : ℝ) ≤ 0.692156176796 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620224996632 : ℝ)) (Q := (0.620224996632 : ℝ))
      (s := (0.784423962888 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786560248350 : ℝ)) (R := (0.787097318428 : ℝ)) (Q2 := (0.620224996632 : ℝ)) (T := (0.832430735633 : ℝ))
    (B := ((6940630853699483/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32036731717/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (216715810621351/312500000000000) := by
  have hk1 : kappa q ≤ 0.617487863567 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512587707472 : ℝ)) (s := (0.858634871263 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619421975380 : ℝ) ≤ 0.691581404506 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619421975380 : ℝ)) (Q := (0.619421975380 : ℝ))
      (s := (0.785058224858 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786050545746 : ℝ)) (R := (0.786587615824 : ℝ)) (Q2 := (0.619421975380 : ℝ)) (T := (0.832085035121 : ℝ))
    (B := ((216715810621351/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511395868667/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929187396762069/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616686843555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511395868667 : ℝ)) (s := (0.859345253964 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618619498565 : ℝ) ≤ 0.691007298337 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618619498565 : ℝ)) (Q := (0.618619498565 : ℝ))
      (s := (0.785690725410 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785540858552 : ℝ)) (R := (0.786077928630 : ℝ)) (Q2 := (0.618619498565 : ℝ)) (T := (0.831739591815 : ℝ))
    (B := ((6929187396762069/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510204029861/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (346173760699503/500000000000000) := by
  have hk1 : kappa q ≤ 0.615886366726 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510204029861 : ℝ)) (s := (0.860053398292 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617817565566 : ℝ) ≤ 0.690433857045 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617817565566 : ℝ)) (Q := (0.617817565566 : ℝ))
      (s := (0.786321470951 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785031186403 : ℝ)) (R := (0.785568256481 : ℝ)) (Q2 := (0.617817565566 : ℝ)) (T := (0.831394405288 : ℝ))
    (B := ((346173760699503/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31813261941/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (54045073291103/78125000000000) := by
  have hk1 : kappa q ≤ 0.615086432462 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509012191056 : ℝ)) (s := (0.860759309771 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617016175764 : ℝ) ≤ 0.689861079389 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617016175764 : ℝ)) (Q := (0.617016175764 : ℝ))
      (s := (0.786950467848 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784521528935 : ℝ)) (R := (0.785058599013 : ℝ)) (Q2 := (0.617016175764 : ℝ)) (T := (0.831049475112 : ℝ))
    (B := ((54045073291103/78125000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2031281409/4000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3456034944154549/5000000000000000) := by
  have hk1 : kappa q ≤ 0.614287040146 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507820352250 : ℝ)) (s := (0.861462993890 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616215328539 : ℝ) ≤ 0.689288964128 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616215328539 : ℝ)) (Q := (0.616215328539 : ℝ))
      (s := (0.787577722434 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784011885781 : ℝ)) (R := (0.784548955859 : ℝ)) (Q2 := (0.616215328539 : ℝ)) (T := (0.830704800859 : ℝ))
    (B := ((3456034944154549/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (101325702689/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906376724906889/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613488189167 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506628513445 : ℝ)) (s := (0.862164456102 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615415023282 : ℝ) ≤ 0.688717510033 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615415023282 : ℝ)) (Q := (0.615415023282 : ℝ))
      (s := (0.788203240998 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783502256581 : ℝ)) (R := (0.784039326659 : ℝ)) (Q2 := (0.615415023282 : ℝ)) (T := (0.830360382107 : ℝ))
    (B := ((6906376724906889/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505436674639/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900689880866839/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612689878915 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505436674639 : ℝ)) (s := (0.862863701827 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614615259378 : ℝ) ≤ 0.688146715870 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614615259378 : ℝ)) (Q := (0.614615259378 : ℝ))
      (s := (0.788827029798 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782992640971 : ℝ)) (R := (0.783529711049 : ℝ)) (Q2 := (0.614615259378 : ℝ)) (T := (0.830016218429 : ℝ))
    (B := ((6900689880866839/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252122417917/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447504673020093/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611892108784 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504244835834 : ℝ)) (s := (0.863560736449 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613816036224 : ℝ) ≤ 0.687576580419 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613816036224 : ℝ)) (Q := (0.613816036224 : ℝ))
      (s := (0.789449095050 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782483038592 : ℝ)) (R := (0.783020108670 : ℝ)) (Q2 := (0.613816036224 : ℝ)) (T := (0.829672309406 : ℝ))
    (B := ((3447504673020093/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125763249257/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889335110316891/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611094878170 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503052997028 : ℝ)) (s := (0.864255565317 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613017353212 : ℝ) ≤ 0.687007102454 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613017353212 : ℝ)) (Q := (0.613017353212 : ℝ))
      (s := (0.790069442936 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781973449083 : ℝ)) (R := (0.782510519161 : ℝ)) (Q2 := (0.613017353212 : ℝ)) (T := (0.829328654616 : ℝ))
    (B := ((6889335110316891/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250930579111/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1720916790906351/2500000000000000) := by
  have hk1 : kappa q ≤ 0.610298186474 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501861158222 : ℝ)) (s := (0.864948193749 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612219209742 : ℝ) ≤ 0.686438280760 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612219209742 : ℝ)) (Q := (0.612219209742 : ℝ))
      (s := (0.790688079601 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781463872085 : ℝ)) (R := (0.782000942163 : ℝ)) (Q2 := (0.612219209742 : ℝ)) (T := (0.828985253641 : ℝ))
    (B := ((1720916790906351/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500669319417/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (429875343495777/625000000000000) := by
  have hk1 : kappa q ≤ 0.609502033099 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500669319417 : ℝ)) (s := (0.865638627024 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611421605216 : ℝ) ≤ 0.685870114125 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611421605216 : ℝ)) (Q := (0.611421605216 : ℝ))
      (s := (0.791305011153 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780954307241 : ℝ)) (R := (0.781491377319 : ℝ)) (Q2 := (0.611421605216 : ℝ)) (T := (0.828642106065 : ℝ))
    (B := ((429875343495777/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499477480611/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3436175048621357/5000000000000000) := by
  have hk1 : kappa q ≤ 0.608706417451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499477480611 : ℝ)) (s := (0.866326870392 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610624539042 : ℝ) ≤ 0.685302601342 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610624539042 : ℝ)) (Q := (0.610624539042 : ℝ))
      (s := (0.791920243661 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780444754195 : ℝ)) (R := (0.780981824273 : ℝ)) (Q2 := (0.610624539042 : ℝ)) (T := (0.828299211473 : ℝ))
    (B := ((3436175048621357/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249142820903/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866700957598791/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607911338940 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498285641806 : ℝ)) (s := (0.867012929068 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609828010625 : ℝ) ≤ 0.684735741205 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609828010625 : ℝ)) (Q := (0.609828010625 : ℝ))
      (s := (0.792533783165 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779935212591 : ℝ)) (R := (0.780472282669 : ℝ)) (Q2 := (0.609828010625 : ℝ)) (T := (0.827956569449 : ℝ))
    (B := ((6866700957598791/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497093803/1000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861058067080779/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607116796976 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497093803000 : ℝ)) (s := (0.867696808234 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609032019378 : ℝ) ≤ 0.684169532515 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609032019378 : ℝ)) (Q := (0.609032019378 : ℝ))
      (s := (0.793145635664 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779425682074 : ℝ)) (R := (0.779962752152 : ℝ)) (Q2 := (0.609032019378 : ℝ)) (T := (0.827614179584 : ℝ))
    (B := ((6861058067080779/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99180392839/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (856927676975769/1250000000000000) := by
  have hk1 : kappa q ≤ 0.606322790978 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495901964195 : ℝ)) (s := (0.868378513039 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608236564714 : ℝ) ≤ 0.683603974076 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608236564714 : ℝ)) (Q := (0.608236564714 : ℝ))
      (s := (0.793755807126 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778916162291 : ℝ)) (R := (0.779453232369 : ℝ)) (Q2 := (0.608236564714 : ℝ)) (T := (0.827272041466 : ℝ))
    (B := ((856927676975769/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494710125389/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3424895496964757/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605529320361 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494710125389 : ℝ)) (s := (0.869058048601 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607441646050 : ℝ) ≤ 0.683039064695 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607441646050 : ℝ)) (Q := (0.607441646050 : ℝ))
      (s := (0.794364303481 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778406652888 : ℝ)) (R := (0.778943722966 : ℝ)) (Q2 := (0.607441646050 : ℝ)) (T := (0.826930154685 : ℝ))
    (B := ((3424895496964757/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493518286583/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422083395821193/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604736384549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493518286583 : ℝ)) (s := (0.869735420004 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606647262809 : ℝ) ≤ 0.682474803187 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606647262809 : ℝ)) (Q := (0.606647262809 : ℝ))
      (s := (0.794971130625 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777897153516 : ℝ)) (R := (0.778434223594 : ℝ)) (Q2 := (0.606647262809 : ℝ)) (T := (0.826588518835 : ℝ))
    (B := ((3422083395821193/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246163223889/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419274399586491/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603943982967 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492326447778 : ℝ)) (s := (0.870410632299 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605853414415 : ℝ) ≤ 0.681911188369 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605853414415 : ℝ)) (Q := (0.605853414415 : ℝ))
      (s := (0.795576294420 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777387663825 : ℝ)) (R := (0.777924733903 : ℝ)) (Q2 := (0.605853414415 : ℝ)) (T := (0.826247133512 : ℝ))
    (B := ((3419274399586491/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122783652243/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416468503392999/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603152115041 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491134608972 : ℝ)) (s := (0.871083690509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605060100291 : ℝ) ≤ 0.681348219060 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605060100291 : ℝ)) (Q := (0.605060100291 : ℝ))
      (s := (0.796179800696 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776878183463 : ℝ)) (R := (0.777415253541 : ℝ)) (Q2 := (0.605060100291 : ℝ)) (T := (0.825905998310 : ℝ))
    (B := ((3416468503392999/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489942770167/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413665702391199/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602360780204 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489942770167 : ℝ)) (s := (0.871754599622 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604267319872 : ℝ) ≤ 0.680785894089 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604267319872 : ℝ)) (Q := (0.604267319872 : ℝ))
      (s := (0.796781655245 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776368712085 : ℝ)) (R := (0.776905782163 : ℝ)) (Q2 := (0.604267319872 : ℝ)) (T := (0.825565112829 : ℝ))
    (B := ((3413665702391199/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488750931361/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821731983499197/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601569977889 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488750931361 : ℝ)) (s := (0.872423364597 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603475072588 : ℝ) ≤ 0.680224212284 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603475072588 : ℝ)) (Q := (0.603475072588 : ℝ))
      (s := (0.797381863830 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775859249342 : ℝ)) (R := (0.776396319420 : ℝ)) (Q2 := (0.603475072588 : ℝ)) (T := (0.825224476668 : ℝ))
    (B := ((6821731983499197/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (121889773139/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3408069366654629/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600779707533 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487559092556 : ℝ)) (s := (0.873089990360 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602683357874 : ℝ) ≤ 0.679663172478 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602683357874 : ℝ)) (Q := (0.602683357874 : ℝ))
      (s := (0.797980432180 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775349794888 : ℝ)) (R := (0.775886864966 : ℝ)) (Q2 := (0.602683357874 : ℝ)) (T := (0.824884089427 : ℝ))
    (B := ((3408069366654629/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (389093803/800000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (272422065784843/400000000000000) := by
  have hk1 : kappa q ≤ 0.599989968576 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486367253750 : ℝ)) (s := (0.873754481809 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601892175172 : ℝ) ≤ 0.679102773511 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601892175172 : ℝ)) (Q := (0.601892175172 : ℝ))
      (s := (0.798577365987 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774840348379 : ℝ)) (R := (0.775377418457 : ℝ)) (Q2 := (0.601892175172 : ℝ)) (T := (0.824543950711 : ℝ))
    (B := ((272422065784843/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15161731717/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402485353939287/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599200760461 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485175414944 : ℝ)) (s := (0.874416843808 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601101523921 : ℝ) ≤ 0.678543014223 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601101523921 : ℝ)) (Q := (0.601101523921 : ℝ))
      (s := (0.799172670917 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774330909470 : ℝ)) (R := (0.774867979548 : ℝ)) (Q2 := (0.601101523921 : ℝ)) (T := (0.824204060123 : ℝ))
    (B := ((3402485353939287/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483983576139/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399697956780451/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598412082636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483983576139 : ℝ)) (s := (0.875077081193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600311403570 : ℝ) ≤ 0.677983893464 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600311403570 : ℝ)) (Q := (0.600311403570 : ℝ))
      (s := (0.799766352596 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773821477820 : ℝ)) (R := (0.774358547898 : ℝ)) (Q2 := (0.600311403570 : ℝ)) (T := (0.823864417270 : ℝ))
    (B := ((3399697956780451/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482791737333/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1698456813045557/2500000000000000) := by
  have hk1 : kappa q ≤ 0.597623934548 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482791737333 : ℝ)) (s := (0.875735198770 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599521813565 : ℝ) ≤ 0.677425410084 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599521813565 : ℝ)) (Q := (0.599521813565 : ℝ))
      (s := (0.800358416624 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773312053086 : ℝ)) (R := (0.773849123164 : ℝ)) (Q2 := (0.599521813565 : ℝ)) (T := (0.823525021761 : ℝ))
    (B := ((1698456813045557/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15049996829/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788264121485561/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596836315652 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481599898528 : ℝ)) (s := (0.876391201313 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598732753359 : ℝ) ≤ 0.676867562937 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598732753359 : ℝ)) (Q := (0.598732753359 : ℝ))
      (s := (0.800948868565 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772802634928 : ℝ)) (R := (0.773339705006 : ℝ)) (Q2 := (0.598732753359 : ℝ)) (T := (0.823185873204 : ℝ))
    (B := ((6788264121485561/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240204029861/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1695676636461181/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596049225402 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480408059722 : ℝ)) (s := (0.877045093570 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597944222406 : ℝ) ≤ 0.676310350884 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597944222406 : ℝ)) (Q := (0.597944222406 : ℝ))
      (s := (0.801537713955 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772293223007 : ℝ)) (R := (0.772830293085 : ℝ)) (Q2 := (0.597944222406 : ℝ)) (T := (0.822846971213 : ℝ))
    (B := ((1695676636461181/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479216220917/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1355431015483353/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595262663256 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479216220917 : ℝ)) (s := (0.877696880256 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597156220161 : ℝ) ≤ 0.675753772787 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597156220161 : ℝ)) (Q := (0.597156220161 : ℝ))
      (s := (0.802124958298 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771783816982 : ℝ)) (R := (0.772320887060 : ℝ)) (Q2 := (0.597156220161 : ℝ)) (T := (0.822508315399 : ℝ))
    (B := ((1355431015483353/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12900 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478024382111/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (677160970684827/1000000000000000) := by
  have hk1 : kappa q ≤ 0.594476628676 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478024382111 : ℝ)) (s := (0.878346566059 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596368746088 : ℝ) ≤ 0.675197827516 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596368746088 : ℝ)) (Q := (0.596368746088 : ℝ))
      (s := (0.802710607062 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771274416519 : ℝ)) (R := (0.771811486597 : ℝ)) (Q2 := (0.596368746088 : ℝ)) (T := (0.822169905378 : ℝ))
    (B := ((677160970684827/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S22
namespace BstLean.Part269.S22
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12900 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052071473873 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S22.wn_upper (by omega : 12900 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010514675607 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035528113773)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010514675607 + 2 * 0.737676 / 12900) := by gcongr
    _ ≤ (0.052071473873 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12900 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12900 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.578166916005 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12900 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.578166916005 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12900 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003333438387 + 0.003240843277 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003333438387 + 0.003240843277 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.578166916005 ≤ R)
    (hB : (X + 0.052071473873 + R + 0.008415138615) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008415138615 := by
    convert (BstLean.Part269.S22.finite_centre_upper (by omega : 12900 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (84862283637/1000000000000)
  | 2 => (8579404709/100000000000)
  | 3 => (86722438239/1000000000000)
  | 4 => (17529704171/200000000000)
  | 5 => (44286796151/500000000000)
  | 6 => (3579968783/40000000000)
  | 7 => (11303409873/125000000000)
  | 8 => (2283999989/25000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003333438387 + 0.003240843277 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218604571859 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010881206417 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003333438387 + 0.003240843277 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220177827177 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010995279001 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003333438387 + 0.003240843277 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221730497049 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011108974812 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003333438387 + 0.003240843277 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223262793125 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011222302110 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003333438387 + 0.003240843277 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224774921668 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011335268919 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003333438387 + 0.003240843277 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226267082072 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011447882915 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003333438387 + 0.003240843277 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227739468752 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011560151563 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12900 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003333438387 + 0.003240843277 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229192269691 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011672082013 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12900 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g) :
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

end BstLean.Part269.S22

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S9
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12575 ≤ n) : wn n ≤ 1.035988328417 := by
  have hnR : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.138307460029 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.138307460029 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035988328417 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12575 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12575 + 24 / (12575 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12575 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008523656225 : ℝ) := by
  have hnR : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.138307460029 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12575 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035988328417 * (81 / 1000 / 12575)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035988328417 * n *
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
        4 * (1 / 2.506628) * 1.035988328417 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035988328417 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035988328417 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12575)) / 112.138307460029 := by gcongr
    _ ≤ (0.008523656225 : ℝ) := by norm_num

end BstLean.Part269.S9
namespace BstLean.Part269.S9
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12575 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12575 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12575 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12575 + 0.008523656225 / 112.138307460029) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12575 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12575 := by gcongr
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
  have hn : (112.138307460029 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S9.finite_centre_upper (by omega : 12575 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (132011770357/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010474312813673/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627927418894 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528047081428 : ℝ)) (s := (0.849215096307 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629912565747 : ℝ) ≤ 0.699112066176 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629912565747 : ℝ)) (Q := (0.629912565747 : ℝ))
      (s := (0.776666054051 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792669561172 : ℝ)) (R := (0.793220511789 : ℝ)) (Q2 := (0.629912565747 : ℝ)) (T := (0.836603075213 : ℝ))
    (B := ((7010474312813673/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52685178957/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502327409951807/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627116955266 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526851789570 : ℝ)) (s := (0.849957170584 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629100618561 : ℝ) ≤ 0.698527512328 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629100618561 : ℝ)) (Q := (0.629100618561 : ℝ))
      (s := (0.777323878269 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792158172072 : ℝ)) (R := (0.792709122689 : ℝ)) (Q2 := (0.629100618561 : ℝ)) (T := (0.836253244449 : ℝ))
    (B := ((3502327409951807/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525656497713/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998841863259791/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626307046322 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525656497713 : ℝ)) (s := (0.850696918070 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628289226710 : ℝ) ≤ 0.697943643812 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628289226710 : ℝ)) (Q := (0.628289226710 : ℝ))
      (s := (0.777979850382 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791646802960 : ℝ)) (R := (0.792197753577 : ℝ)) (Q2 := (0.628289226710 : ℝ)) (T := (0.835903677679 : ℝ))
    (B := ((6998841863259791/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16389412683/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1748258857985571/2500000000000000) := by
  have hk1 : kappa q ≤ 0.625497691398 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524461205856 : ℝ)) (s := (0.851434344828 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478389530 : ℝ) ≤ 0.697360459321 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478389530 : ℝ)) (Q := (0.627478389530 : ℝ))
      (s := (0.778633977343 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791135453455 : ℝ)) (R := (0.791686404072 : ℝ)) (Q2 := (0.627478389530 : ℝ)) (T := (0.835554374451 : ℝ))
    (B := ((1748258857985571/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523265913999/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1746808878763669/2500000000000000) := by
  have hk1 : kappa q ≤ 0.624688889833 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523265913999 : ℝ)) (s := (0.852169456885 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668106357 : ℝ) ≤ 0.696777957554 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668106357 : ℝ)) (Q := (0.626668106357 : ℝ))
      (s := (0.779286266064 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790624123176 : ℝ)) (R := (0.791175073793 : ℝ)) (Q2 := (0.626668106357 : ℝ)) (T := (0.835205334315 : ℝ))
    (B := ((1746808878763669/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522070622141/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981442101743789/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623880640967 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522070622141 : ℝ)) (s := (0.852902260226 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625858376531 : ℝ) ≤ 0.696196137213 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625858376531 : ℝ)) (Q := (0.625858376531 : ℝ))
      (s := (0.779936723412 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790112811744 : ℝ)) (R := (0.790663762361 : ℝ)) (Q2 := (0.625858376531 : ℝ)) (T := (0.834856556823 : ℝ))
    (B := ((6981442101743789/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130218832571/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3487827590599701/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623072944149 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520875330284 : ℝ)) (s := (0.853632760795 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625049199400 : ℝ) ≤ 0.695614997005 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625049199400 : ℝ)) (Q := (0.625049199400 : ℝ))
      (s := (0.780585356210 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789601518783 : ℝ)) (R := (0.790152469400 : ℝ)) (Q2 := (0.625049199400 : ℝ)) (T := (0.834508041529 : ℝ))
    (B := ((3487827590599701/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519680038427/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969874742653993/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622265798724 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519680038427 : ℝ)) (s := (0.854360964500 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624240574306 : ℝ) ≤ 0.695034535640 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624240574306 : ℝ)) (Q := (0.624240574306 : ℝ))
      (s := (0.781232171247 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789090243913 : ℝ)) (R := (0.789641194530 : ℝ)) (Q2 := (0.624240574306 : ℝ)) (T := (0.834159787988 : ℝ))
    (B := ((6969874742653993/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51848474657/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (108814074615351/156250000000000) := by
  have hk1 : kappa q ≤ 0.621459204045 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518484746570 : ℝ)) (s := (0.855086877209 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623432500603 : ℝ) ≤ 0.694454751833 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623432500603 : ℝ)) (Q := (0.623432500603 : ℝ))
      (s := (0.781877175260 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788578986760 : ℝ)) (R := (0.789129937377 : ℝ)) (Q2 := (0.623432500603 : ℝ)) (T := (0.833811795756 : ℝ))
    (B := ((108814074615351/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64661181839/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3479166634350939/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620653159465 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517289454712 : ℝ)) (s := (0.855810504752 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622624977643 : ℝ) ≤ 0.693875644302 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622624977643 : ℝ)) (Q := (0.622624977643 : ℝ))
      (s := (0.782520374953 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788067746948 : ℝ)) (R := (0.788618697565 : ℝ)) (Q2 := (0.622624977643 : ℝ)) (T := (0.833464064391 : ℝ))
    (B := ((3479166634350939/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103218832571/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952572211971201/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619847664343 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516094162855 : ℝ)) (s := (0.856531852921 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621818004782 : ℝ) ≤ 0.693297211771 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621818004782 : ℝ)) (Q := (0.621818004782 : ℝ))
      (s := (0.783161776985 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787556524103 : ℝ)) (R := (0.788107474720 : ℝ)) (Q2 := (0.621818004782 : ℝ)) (T := (0.833116593452 : ℝ))
    (B := ((6952572211971201/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257449435499/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1736704398647759/2500000000000000) := by
  have hk1 : kappa q ≤ 0.619042718039 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514898870998 : ℝ)) (s := (0.857250927469 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621011581382 : ℝ) ≤ 0.692719452967 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621011581382 : ℝ)) (Q := (0.621011581382 : ℝ))
      (s := (0.783801387974 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787045317853 : ℝ)) (R := (0.787596268470 : ℝ)) (Q2 := (0.621011581382 : ℝ)) (T := (0.832769382500 : ℝ))
    (B := ((1736704398647759/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25685178957/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6941069406003371/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618238319916 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513703579140 : ℝ)) (s := (0.857967734113 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620205706800 : ℝ) ≤ 0.692142366617 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620205706800 : ℝ)) (Q := (0.620205706800 : ℝ))
      (s := (0.784439214505 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786534127823 : ℝ)) (R := (0.787085078440 : ℝ)) (Q2 := (0.620205706800 : ℝ)) (T := (0.832422431095 : ℝ))
    (B := ((6941069406003371/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512508287283/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935327635691321/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617434469343 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512508287283 : ℝ)) (s := (0.858682278533 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619400380409 : ℝ) ≤ 0.691565951463 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619400380409 : ℝ)) (Q := (0.619400380409 : ℝ))
      (s := (0.785075263112 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786022953646 : ℝ)) (R := (0.786573904263 : ℝ)) (Q2 := (0.619400380409 : ℝ)) (T := (0.832075738805 : ℝ))
    (B := ((6935327635691321/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255656497713/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929592273178873/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616631165688 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511312995426 : ℝ)) (s := (0.859394566372 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618595601572 : ℝ) ≤ 0.690990206238 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618595601572 : ℝ)) (Q := (0.618595601572 : ℝ))
      (s := (0.785709540299 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785511794948 : ℝ)) (R := (0.786062745565 : ℝ)) (Q2 := (0.618595601572 : ℝ)) (T := (0.831729305192 : ℝ))
    (B := ((6929592273178873/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510117703569/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923863308030641/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615828408324 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510117703569 : ℝ)) (s := (0.860104603235 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617791369663 : ℝ) ≤ 0.690415129688 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617791369663 : ℝ)) (Q := (0.617791369663 : ℝ))
      (s := (0.786342052526 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785000651362 : ℝ)) (R := (0.785551601979 : ℝ)) (Q2 := (0.617791369663 : ℝ)) (T := (0.831383129823 : ℝ))
    (B := ((6923863308030641/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508922411711/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918140729851611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615026196628 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508922411711 : ℝ)) (s := (0.860812394694 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616987684058 : ℝ) ≤ 0.689840720562 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616987684058 : ℝ)) (Q := (0.616987684058 : ℝ))
      (s := (0.786972806215 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784489522520 : ℝ)) (R := (0.785040473137 : ℝ)) (Q2 := (0.616987684058 : ℝ)) (T := (0.831037212268 : ℝ))
    (B := ((6918140729851611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253863559927/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912424528286897/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614224529980 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507727119854 : ℝ)) (s := (0.861517946282 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616184544133 : ℝ) ≤ 0.689266977608 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616184544133 : ℝ)) (Q := (0.616184544133 : ℝ))
      (s := (0.787601807751 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783978408054 : ℝ)) (R := (0.784529358671 : ℝ)) (Q2 := (0.616184544133 : ℝ)) (T := (0.830691552095 : ℝ))
    (B := ((6912424528286897/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506531827997/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906714693021499/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613423407761 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506531827997 : ℝ)) (s := (0.862221263497 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615381949272 : ℝ) ≤ 0.688693899586 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615381949272 : ℝ)) (Q := (0.615381949272 : ℝ))
      (s := (0.788229063478 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783467307599 : ℝ)) (R := (0.784018258216 : ℝ)) (Q2 := (0.615381949272 : ℝ)) (T := (0.830346148878 : ℝ))
    (B := ((6906714693021499/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505336536139/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6901011213780057/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612622829357 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505336536139 : ℝ)) (s := (0.862922351805 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614579898858 : ℝ) ≤ 0.688121485255 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614579898858 : ℝ)) (Q := (0.614579898858 : ℝ))
      (s := (0.788854579704 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782956220789 : ℝ)) (R := (0.783507171406 : ℝ)) (Q2 := (0.614579898858 : ℝ)) (T := (0.830001002188 : ℝ))
    (B := ((6901011213780057/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252070622141/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895314080326611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611822794157 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504141244282 : ℝ)) (s := (0.863621216631 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613778392278 : ℝ) ≤ 0.687549733377 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613778392278 : ℝ)) (Q := (0.613778392278 : ℝ))
      (s := (0.789478362701 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782445147261 : ℝ)) (R := (0.782996097878 : ℝ)) (Q2 := (0.613778392278 : ℝ)) (T := (0.829656111600 : ℝ))
    (B := ((6895314080326611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20117838097/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889623282464367/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611023301554 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502945952425 : ℝ)) (s := (0.864317863370 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612977428924 : ℝ) ≤ 0.686978642724 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612977428924 : ℝ)) (Q := (0.612977428924 : ℝ))
      (s := (0.790100418700 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781934086652 : ℝ)) (R := (0.782485037269 : ℝ)) (Q2 := (0.612977428924 : ℝ)) (T := (0.829311476690 : ℝ))
    (B := ((6889623282464367/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62718832571/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1376787762007091/2000000000000000) := by
  have hk1 : kappa q ≤ 0.610224350941 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501750660568 : ℝ)) (s := (0.865012297381 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612177008191 : ℝ) ≤ 0.686408212069 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612177008191 : ℝ)) (Q := (0.612177008191 : ℝ))
      (s := (0.790720753897 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781423038601 : ℝ)) (R := (0.781973989218 : ℝ)) (Q2 := (0.612177008191 : ℝ)) (T := (0.828967097039 : ℝ))
    (B := ((1376787762007091/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50055536871/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878260652920699/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609425941717 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500555368710 : ℝ)) (s := (0.865704523990 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611377129472 : ℝ) ≤ 0.685838440185 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611377129472 : ℝ)) (Q := (0.611377129472 : ℝ))
      (s := (0.791339374453 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780912002745 : ℝ)) (R := (0.781462953362 : ℝ)) (Q2 := (0.611377129472 : ℝ)) (T := (0.828622972221 : ℝ))
    (B := ((6878260652920699/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499360076853/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (859073600129923/1250000000000000) := by
  have hk1 : kappa q ≤ 0.608628073284 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499360076853 : ℝ)) (s := (0.866394548486 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610577792173 : ℝ) ≤ 0.685269325859 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610577792173 : ℝ)) (Q := (0.610577792173 : ℝ))
      (s := (0.791956286487 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780400978728 : ℝ)) (R := (0.780951929345 : ℝ)) (Q2 := (0.610577792173 : ℝ)) (T := (0.828279101823 : ℝ))
    (B := ((859073600129923/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (124541196249/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (274676929773961/400000000000000) := by
  have hk1 : kappa q ≤ 0.607830745045 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498164784996 : ℝ)) (s := (0.867082376127 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609778995691 : ℝ) ≤ 0.684700867872 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609778995691 : ℝ)) (Q := (0.609778995691 : ℝ))
      (s := (0.792571496090 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779889966187 : ℝ)) (R := (0.780440916804 : ℝ)) (Q2 := (0.609778995691 : ℝ)) (T := (0.827935485423 : ℝ))
    (B := ((274676929773961/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496969493139/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (343063198642257/500000000000000) := by
  have hk1 : kappa q ≤ 0.607033956410 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496969493139 : ℝ)) (s := (0.867768012138 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608980739439 : ℝ) ≤ 0.684133065019 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608980739439 : ℝ)) (Q := (0.608980739439 : ℝ))
      (s := (0.793185009309 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779378964769 : ℝ)) (R := (0.779929915386 : ℝ)) (Q2 := (0.608980739439 : ℝ)) (T := (0.827592122610 : ℝ))
    (B := ((343063198642257/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495774201281/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855610976561021/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606237706786 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495774201281 : ℝ)) (s := (0.868451461709 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608183022822 : ℝ) ≤ 0.683565916090 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608183022822 : ℝ)) (Q := (0.608183022822 : ℝ))
      (s := (0.793796832163 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778867974114 : ℝ)) (R := (0.779418924731 : ℝ)) (Q2 := (0.608183022822 : ℝ)) (T := (0.827249012967 : ℝ))
    (B := ((6855610976561021/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30911181839/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1369992849113503/2000000000000000) := by
  have hk1 : kappa q ≤ 0.605441995591 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494578909424 : ℝ)) (s := (0.869132729998 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607385845256 : ℝ) ≤ 0.682999419886 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607385845256 : ℝ)) (Q := (0.607385845256 : ℝ))
      (s := (0.794406970629 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778356993870 : ℝ)) (R := (0.778907944487 : ℝ)) (Q2 := (0.607385845256 : ℝ)) (T := (0.826906156084 : ℝ))
    (B := ((1369992849113503/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493383617567/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1711080942493199/2500000000000000) := by
  have hk1 : kappa q ≤ 0.604646822239 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493383617567 : ℝ)) (s := (0.869811822130 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606589206153 : ℝ) ≤ 0.682433575208 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606589206153 : ℝ)) (Q := (0.606589206153 : ℝ))
      (s := (0.795015430655 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777846023679 : ℝ)) (R := (0.778396974296 : ℝ)) (Q2 := (0.606589206153 : ℝ)) (T := (0.826563551548 : ℝ))
    (B := ((1711080942493199/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492188325709/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419344769961073/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603852186151 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492188325709 : ℝ)) (s := (0.870488743199 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605793104935 : ℝ) ≤ 0.681868380864 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605793104935 : ℝ)) (Q := (0.605793104935 : ℝ))
      (s := (0.795622218150 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777335063191 : ℝ)) (R := (0.777886013808 : ℝ)) (Q2 := (0.605793104935 : ℝ)) (T := (0.826221198952 : ℝ))
    (B := ((3419344769961073/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122748258463/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (341653077279887/500000000000000) := by
  have hk1 : kappa q ≤ 0.603058086751 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490993033852 : ℝ)) (s := (0.871163498265 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604997541024 : ℝ) ≤ 0.681303835667 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604997541024 : ℝ)) (Q := (0.604997541024 : ℝ))
      (s := (0.796227338990 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776824112052 : ℝ)) (R := (0.777375062669 : ℝ)) (Q2 := (0.604997541024 : ℝ)) (T := (0.825879097889 : ℝ))
    (B := ((341653077279887/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97959548399/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413719888609211/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602264523465 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489797741995 : ℝ)) (s := (0.871836092358 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604202513846 : ℝ) ≤ 0.680739938432 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604202513846 : ℝ)) (Q := (0.604202513846 : ℝ))
      (s := (0.796830799018 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776313169913 : ℝ)) (R := (0.776864120530 : ℝ)) (Q2 := (0.604202513846 : ℝ)) (T := (0.825537247954 : ℝ))
    (B := ((3413719888609211/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244301225069/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3410912112519749/5000000000000000) := by
  have hk1 : kappa q ≤ 0.601471495722 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488602450138 : ℝ)) (s := (0.872506530474 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603408022827 : ℝ) ≤ 0.680176687977 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603408022827 : ℝ)) (Q := (0.603408022827 : ℝ))
      (s := (0.797432604042 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775802236422 : ℝ)) (R := (0.776353187039 : ℝ)) (Q2 := (0.603408022827 : ℝ)) (T := (0.825195648742 : ℝ))
    (B := ((3410912112519749/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12185178957/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3408107439676257/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600679002953 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487407158280 : ℝ)) (s := (0.873174817581 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602614067397 : ℝ) ≤ 0.679614083126 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602614067397 : ℝ)) (Q := (0.602614067397 : ℝ))
      (s := (0.798032759839 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775291311229 : ℝ)) (R := (0.775842261846 : ℝ)) (Q2 := (0.602614067397 : ℝ)) (T := (0.824854299851 : ℝ))
    (B := ((3408107439676257/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486211866423/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405305865242527/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599887044597 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486211866423 : ℝ)) (s := (0.873840958613 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601820646997 : ℝ) ≤ 0.679052122712 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601820646997 : ℝ)) (Q := (0.601820646997 : ℝ))
      (s := (0.798631272146 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774780393990 : ℝ)) (R := (0.775331344607 : ℝ)) (Q2 := (0.601820646997 : ℝ)) (T := (0.824513200882 : ℝ))
    (B := ((3405305865242527/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (242508287283/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6805014768800521/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599095620091 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485016574566 : ℝ)) (s := (0.874504958475 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601027761061 : ℝ) ≤ 0.678490805565 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601027761061 : ℝ)) (Q := (0.601027761061 : ℝ))
      (s := (0.799228146673 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774269484357 : ℝ)) (R := (0.774820434974 : ℝ)) (Q2 := (0.601027761061 : ℝ)) (T := (0.824172351436 : ℝ))
    (B := ((6805014768800521/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483821282709/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1359884796939587/2000000000000000) := by
  have hk1 : kappa q ≤ 0.598304728878 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483821282709 : ℝ)) (s := (0.875166822039 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600235409029 : ℝ) ≤ 0.677930130521 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600235409029 : ℝ)) (Q := (0.600235409029 : ℝ))
      (s := (0.799823389098 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773758581983 : ℝ)) (R := (0.774309532600 : ℝ)) (Q2 := (0.600235409029 : ℝ)) (T := (0.823831751115 : ℝ))
    (B := ((1359884796939587/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482625990851/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (271753574744469/400000000000000) := by
  have hk1 : kappa q ≤ 0.597514370400 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482625990851 : ℝ)) (s := (0.875826554151 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599443590346 : ℝ) ≤ 0.677370096424 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599443590346 : ℝ)) (Q := (0.599443590346 : ℝ))
      (s := (0.800417005063 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773247686524 : ℝ)) (R := (0.773798637141 : ℝ)) (Q2 := (0.599443590346 : ℝ)) (T := (0.823491399526 : ℝ))
    (B := ((271753574744469/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240715349497/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788260911011523/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596724544109 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481430698994 : ℝ)) (s := (0.876484159621 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598652304461 : ℝ) ≤ 0.676810702120 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598652304461 : ℝ)) (Q := (0.598652304461 : ℝ))
      (s := (0.801009000177 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772736797638 : ℝ)) (R := (0.773287748255 : ℝ)) (Q2 := (0.598652304461 : ℝ)) (T := (0.823151296275 : ℝ))
    (B := ((6788260911011523/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480235407137/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1356537499854933/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595935249454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480235407137 : ℝ)) (s := (0.877139643234 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597861550820 : ℝ) ≤ 0.676251946457 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597861550820 : ℝ)) (Q := (0.597861550820 : ℝ))
      (s := (0.801599380022 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772225914981 : ℝ)) (R := (0.772776865598 : ℝ)) (Q2 := (0.597861550820 : ℝ)) (T := (0.822811440969 : ℝ))
    (B := ((1356537499854933/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479040115279/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1355424026932491/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595146485888 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479040115279 : ℝ)) (s := (0.877793009743 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597071328879 : ℝ) ≤ 0.675693828289 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597071328879 : ℝ)) (Q := (0.597071328879 : ℝ))
      (s := (0.802188150144 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771715038212 : ℝ)) (R := (0.772265988829 : ℝ)) (Q2 := (0.597071328879 : ℝ)) (T := (0.822471833219 : ℝ))
    (B := ((1355424026932491/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12575 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (238922411711/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385779451390037/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594358252871 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477844823422 : ℝ)) (s := (0.878444263872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596281638094 : ℝ) ≤ 0.675136346477 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596281638094 : ℝ)) (Q := (0.596281638094 : ℝ))
      (s := (0.802775316058 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771204166992 : ℝ)) (R := (0.771755117609 : ℝ)) (Q2 := (0.596281638094 : ℝ)) (T := (0.822132472637 : ℝ))
    (B := ((3385779451390037/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S9
namespace BstLean.Part269.S9
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12575 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052747359756 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S9.wn_upper (by omega : 12575 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010649684378 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035988328417)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010649684378 + 2 * 0.737676 / 12575) := by gcongr
    _ ≤ (0.052747359756 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12575 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12575 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.138307460029 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12575 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.138307460029 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12575 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003622837465 + 0.003327558274 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003622837465 + 0.003327558274 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.138307460029 ≤ R)
    (hB : (X + 0.052747359756 + R + 0.008523656225) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008523656225 := by
    convert (BstLean.Part269.S9.finite_centre_upper (by omega : 12575 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (4289526273/50000000000)
  | 2 => (43369461669/500000000000)
  | 3 => (21921576497/250000000000)
  | 4 => (88634284607/1000000000000)
  | 5 => (2799525043/31250000000)
  | 6 => (45270088877/500000000000)
  | 7 => (1830063343/20000000000)
  | 8 => (92477011993/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003622837465 + 0.003327558274 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219359282744 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011020921455 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003622837465 + 0.003327558274 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220928576069 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011136458735 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003622837465 + 0.003327558274 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222477409013 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011251614404 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003622837465 + 0.003327558274 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224005988869 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011366396829 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003622837465 + 0.003327558274 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225514517763 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011480814135 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003622837465 + 0.003327558274 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227003191158 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011594874097 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003622837465 + 0.003327558274 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228472199731 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011708584279 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12575 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003622837465 + 0.003327558274 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229921727908 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011821951920 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12575 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g) :
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

end BstLean.Part269.S9

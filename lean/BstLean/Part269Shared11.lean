import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S11
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12625 ≤ n) : wn n ≤ 1.035916364443 := by
  have hnR : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.361025271221 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.361025271221 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035916364443 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12625 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12625 + 24 / (12625 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12625 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008506688079 : ℝ) := by
  have hnR : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.361025271221 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12625 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035916364443 * (81 / 1000 / 12625)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035916364443 * n *
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
        4 * (1 / 2.506628) * 1.035916364443 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035916364443 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035916364443 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12625)) / 112.361025271221 := by gcongr
    _ ≤ (0.008506688079 : ℝ) := by norm_num

end BstLean.Part269.S11
namespace BstLean.Part269.S11
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12625 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12625 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12625 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12625 + 0.008506688079 / 112.361025271221) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12625 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12625 := by gcongr
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
  have hn : (112.361025271221 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S11.finite_centre_upper (by omega : 12625 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264026241043/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (87629662287689/125000000000000) := by
  have hk1 : kappa q ≤ 0.627931082052 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528052482086 : ℝ)) (s := (0.849211738122 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629911192503 : ℝ) ≤ 0.699111077280 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629911192503 : ℝ)) (Q := (0.629911192503 : ℝ))
      (s := (0.776667167814 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792670878522 : ℝ)) (R := (0.793219647156 : ℝ)) (Q2 := (0.629911192503 : ℝ)) (T := (0.836602483524 : ℝ))
    (B := ((87629662287689/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263428865147/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502278099001047/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627120981982 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526857730294 : ℝ)) (s := (0.849953488157 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629099611774 : ℝ) ≤ 0.698526787679 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629099611774 : ℝ)) (Q := (0.629099611774 : ℝ))
      (s := (0.777324693077 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792159719745 : ℝ)) (R := (0.792708488379 : ℝ)) (Q2 := (0.629099611774 : ℝ)) (T := (0.836252810687 : ℝ))
    (B := ((3502278099001047/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525662978503/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499372971635063/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626311436098 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525662978503 : ℝ)) (s := (0.850692913472 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628288585882 : ℝ) ≤ 0.697943182792 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628288585882 : ℝ)) (Q := (0.628288585882 : ℝ))
      (s := (0.777980367909 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791648580939 : ℝ)) (R := (0.792197349573 : ℝ)) (Q2 := (0.628288585882 : ℝ)) (T := (0.835903401605 : ℝ))
    (B := ((3499372971635063/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524468226711/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496471103947113/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625502443737 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524468226711 : ℝ)) (s := (0.851430020126 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478114162 : ℝ) ≤ 0.697360261315 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478114162 : ℝ)) (Q := (0.627478114162 : ℝ))
      (s := (0.778634199254 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791137461723 : ℝ)) (R := (0.791686230357 : ℝ)) (Q2 := (0.627478114162 : ℝ)) (T := (0.835554255828 : ℝ))
    (B := ((3496471103947113/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (13081836873/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3493572490496417/5000000000000000) := by
  have hk1 : kappa q ≤ 0.624694004238 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523273474920 : ℝ)) (s := (0.852164814133 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668195954 : ℝ) ≤ 0.696778021949 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668195954 : ℝ)) (Q := (0.626668195954 : ℝ))
      (s := (0.779286194014 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790626361718 : ℝ)) (R := (0.791175130352 : ℝ)) (Q2 := (0.626668195954 : ℝ)) (T := (0.835205372909 : ℝ))
    (B := ((3493572490496417/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65259840391/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3490677125863773/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623886116945 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522078723128 : ℝ)) (s := (0.852897301472 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625858830597 : ℝ) ≤ 0.696196463396 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625858830597 : ℝ)) (Q := (0.625858830597 : ℝ))
      (s := (0.779936359048 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790115280544 : ℝ)) (R := (0.790664049178 : ℝ)) (Q2 := (0.625858830597 : ℝ)) (T := (0.834856752397 : ℝ))
    (B := ((3490677125863773/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520883971337/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3487785004651421/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623078781204 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520883971337 : ℝ)) (s := (0.853627488080 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625050017439 : ℝ) ≤ 0.695615584367 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625050017439 : ℝ)) (Q := (0.625050017439 : ℝ))
      (s := (0.780584701170 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789604217826 : ℝ)) (R := (0.790152986460 : ℝ)) (Q2 := (0.625050017439 : ℝ)) (T := (0.834508393849 : ℝ))
    (B := ((3487785004651421/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103937843909/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969792242965819/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622271996363 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519689219545 : ℝ)) (s := (0.854355379856 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624241755826 : ℝ) ≤ 0.695035383573 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624241755826 : ℝ)) (Q := (0.624241755826 : ℝ))
      (s := (0.781231227156 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789093173185 : ℝ)) (R := (0.789641941819 : ℝ)) (Q2 := (0.624241755826 : ℝ)) (T := (0.834160296820 : ℝ))
    (B := ((6969792242965819/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259247233877/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964020942005923/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621465761775 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518494467754 : ℝ)) (s := (0.855080982661 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623434045110 : ℝ) ≤ 0.694455859731 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623434045110 : ℝ)) (Q := (0.623434045110 : ℝ))
      (s := (0.781875943740 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788582146247 : ℝ)) (R := (0.789130914881 : ℝ)) (Q2 := (0.623434045110 : ℝ)) (T := (0.833812460867 : ℝ))
    (B := ((6964020942005923/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258649857981/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958256095754689/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620660076796 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517299715962 : ℝ)) (s := (0.855804302318 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622626884644 : ℝ) ≤ 0.693877011559 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622626884644 : ℝ)) (Q := (0.622626884644 : ℝ))
      (s := (0.782518857613 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788071136637 : ℝ)) (R := (0.788619905271 : ℝ)) (Q2 := (0.622626884644 : ℝ)) (T := (0.833464885546 : ℝ))
    (B := ((6958256095754689/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516104964171/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3476248846792737/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619854940783 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516104964171 : ℝ)) (s := (0.856525344610 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621820273787 : ℝ) ≤ 0.693298837785 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621820273787 : ℝ)) (Q := (0.621820273787 : ℝ))
      (s := (0.783159975425 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787560143981 : ℝ)) (R := (0.788108912615 : ℝ)) (Q2 := (0.621820273787 : ℝ)) (T := (0.833117570420 : ℝ))
    (B := ((3476248846792737/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514910212379/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473372862456601/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619050353097 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514910212379 : ℝ)) (s := (0.857244115284 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621014211897 : ℝ) ≤ 0.692721337134 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621014211897 : ℝ)) (Q := (0.621014211897 : ℝ))
      (s := (0.783799303791 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787049167906 : ℝ)) (R := (0.787597936540 : ℝ)) (Q2 := (0.621014211897 : ℝ)) (T := (0.832770515047 : ℝ))
    (B := ((3473372862456601/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128428865147/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (867625022399263/1250000000000000) := by
  have hk1 : kappa q ≤ 0.618246313105 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513715460588 : ℝ)) (s := (0.857960620048 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620208698340 : ℝ) ≤ 0.692144508341 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620208698340 : ℝ)) (Q := (0.620208698340 : ℝ))
      (s := (0.784436849277 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786538208042 : ℝ)) (R := (0.787086976676 : ℝ)) (Q2 := (0.620208698340 : ℝ)) (T := (0.832423718993 : ℝ))
    (B := ((867625022399263/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128130177199/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3467630522962733/5000000000000000) := by
  have hk1 : kappa q ≤ 0.617442820172 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512520708796 : ℝ)) (s := (0.858674864577 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619403732479 : ℝ) ≤ 0.691568350141 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619403732479 : ℝ)) (Q := (0.619403732479 : ℝ))
      (s := (0.785072618419 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786027264016 : ℝ)) (R := (0.786576032650 : ℝ)) (Q2 := (0.619403732479 : ℝ)) (T := (0.832077181820 : ℝ))
    (B := ((3467630522962733/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102265191401/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (55436226517163/80000000000000) := by
  have hk1 : kappa q ≤ 0.616639873670 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511325957005 : ℝ)) (s := (0.859386854504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618599313687 : ℝ) ≤ 0.690992861277 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618599313687 : ℝ)) (Q := (0.618599313687 : ℝ))
      (s := (0.785706617706 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785516335460 : ℝ)) (R := (0.786065104094 : ℝ)) (Q2 := (0.618599313687 : ℝ)) (T := (0.831730903096 : ℝ))
    (B := ((55436226517163/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510131205213/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (692380197493247/1000000000000000) := by
  have hk1 : kappa q ≤ 0.615837472973 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510131205213 : ℝ)) (s := (0.860096595429 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617795441335 : ℝ) ≤ 0.690418040493 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617795441335 : ℝ)) (Q := (0.617795441335 : ℝ))
      (s := (0.786338853591 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785005422005 : ℝ)) (R := (0.785554190639 : ℝ)) (Q2 := (0.617795441335 : ℝ)) (T := (0.831384882386 : ℝ))
    (B := ((692380197493247/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (254468226711/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918082016405691/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615035617458 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508936453422 : ℝ)) (s := (0.860804092915 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616992114801 : ℝ) ≤ 0.689843886538 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616992114801 : ℝ)) (Q := (0.616992114801 : ℝ))
      (s := (0.786969332486 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784494523284 : ℝ)) (R := (0.785043291918 : ℝ)) (Q2 := (0.616992114801 : ℝ)) (T := (0.831039119260 : ℝ))
    (B := ((6918082016405691/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50774170163/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3456184214362017/5000000000000000) := by
  have hk1 : kappa q ≤ 0.614234306505 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507741701630 : ℝ)) (s := (0.861509352489 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616189333462 : ℝ) ≤ 0.689270398167 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616189333462 : ℝ)) (Q := (0.616189333462 : ℝ))
      (s := (0.787598060770 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783983638930 : ℝ)) (R := (0.784532407564 : ℝ)) (Q2 := (0.616189333462 : ℝ)) (T := (0.830693613289 : ℝ))
    (B := ((3456184214362017/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506546949839/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (863332650198289/1250000000000000) := by
  have hk1 : kappa q ≤ 0.613433539497 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506546949839 : ℝ)) (s := (0.862212379643 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615387096700 : ℝ) ≤ 0.688697574135 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615387096700 : ℝ)) (Q := (0.615387096700 : ℝ))
      (s := (0.788225044778 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783472768577 : ℝ)) (R := (0.784021537211 : ℝ)) (Q2 := (0.615387096700 : ℝ)) (T := (0.830348364045 : ℝ))
    (B := ((863332650198289/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505352198047/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1380192064946181/2000000000000000) := by
  have hk1 : kappa q ≤ 0.612633315821 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505352198047 : ℝ)) (s := (0.862913179833 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614585403901 : ℝ) ≤ 0.688125413205 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614585403901 : ℝ)) (Q := (0.614585403901 : ℝ))
      (s := (0.788850290811 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782961911861 : ℝ)) (R := (0.783510680495 : ℝ)) (Q2 := (0.614585403901 : ℝ)) (T := (0.830003371100 : ℝ))
    (B := ((1380192064946181/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31509840391/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895265787935527/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611833634867 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504157446256 : ℝ)) (s := (0.863611758480 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613784254455 : ℝ) ≤ 0.687553914145 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613784254455 : ℝ)) (Q := (0.613784254455 : ℝ))
      (s := (0.789473805128 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782451068420 : ℝ)) (R := (0.782999837054 : ℝ)) (Q2 := (0.613784254455 : ℝ)) (T := (0.829658634031 : ℝ))
    (B := ((6895265787935527/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100592538893/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (861197197627123/1250000000000000) := by
  have hk1 : kappa q ≤ 0.611034496026 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502962694465 : ℝ)) (s := (0.864308120972 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612983647752 : ℝ) ≤ 0.686983075724 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612983647752 : ℝ)) (Q := (0.612983647752 : ℝ))
      (s := (0.790095593956 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781940237890 : ℝ)) (R := (0.782489006524 : ℝ)) (Q2 := (0.612983647752 : ℝ)) (T := (0.829314152415 : ℝ))
    (B := ((861197197627123/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501767942673/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883895693830941/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610235898695 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501767942673 : ℝ)) (s := (0.865002272660 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612183583185 : ℝ) ≤ 0.686412896715 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612183583185 : ℝ)) (Q := (0.612183583185 : ℝ))
      (s := (0.790715663484 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781429419909 : ℝ)) (R := (0.781978188543 : ℝ)) (Q2 := (0.612183583185 : ℝ)) (T := (0.828969925830 : ℝ))
    (B := ((6883895693830941/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250286595441/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (859777514533961/1250000000000000) := by
  have hk1 : kappa q ≤ 0.609437842273 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500573190882 : ℝ)) (s := (0.865694218862 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611384060155 : ℝ) ≤ 0.685843375900 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611384060155 : ℝ)) (Q := (0.611384060155 : ℝ))
      (s := (0.791334019861 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780918614119 : ℝ)) (R := (0.781467382753 : ℝ)) (Q2 := (0.611384060155 : ℝ)) (T := (0.828625953856 : ℝ))
    (B := ((859777514533961/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49937843909/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1718137709567977/2500000000000000) := by
  have hk1 : kappa q ≤ 0.608640326161 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499378439090 : ℝ)) (s := (0.866383964864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610585078061 : ℝ) ≤ 0.685274512059 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610585078061 : ℝ)) (Q := (0.610585078061 : ℝ))
      (s := (0.791950669202 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780407820159 : ℝ)) (R := (0.780956588793 : ℝ)) (Q2 := (0.610585078061 : ℝ)) (T := (0.828282236074 : ℝ))
    (B := ((1718137709567977/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498183687299/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433443924901223/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607843349765 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498183687299 : ℝ)) (s := (0.867071515914 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609786636308 : ℝ) ≤ 0.684706303981 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609786636308 : ℝ)) (Q := (0.609786636308 : ℝ))
      (s := (0.792565617587 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779897037672 : ℝ)) (R := (0.780445806306 : ℝ)) (Q2 := (0.609786636308 : ℝ)) (T := (0.827938772069 : ℝ))
    (B := ((3433443924901223/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496988935507/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1715307785218021/2500000000000000) := by
  have hk1 : kappa q ≤ 0.607046912494 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496988935507 : ℝ)) (s := (0.867756877233 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608988734304 : ℝ) ≤ 0.684138750457 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608988734304 : ℝ)) (Q := (0.608988734304 : ℝ))
      (s := (0.793178871057 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779386266301 : ℝ)) (R := (0.779935034935 : ℝ)) (Q2 := (0.608988734304 : ℝ)) (T := (0.827595561425 : ℝ))
    (B := ((1715307785218021/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123948545929/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3427790350763657/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606251013758 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495794183716 : ℝ)) (s := (0.868440054002 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608191371457 : ℝ) ≤ 0.683571850283 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608191371457 : ℝ)) (Q := (0.608191371457 : ℝ))
      (s := (0.793790435623 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778875505689 : ℝ)) (R := (0.779424274323 : ℝ)) (Q2 := (0.608191371457 : ℝ)) (T := (0.827252603729 : ℝ))
    (B := ((3427790350763657/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123649857981/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3424968260926057/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605455652972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494599431924 : ℝ)) (s := (0.869121051374 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607394547182 : ℝ) ≤ 0.683005602260 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607394547182 : ℝ)) (Q := (0.607394547182 : ℝ))
      (s := (0.794400317255 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778364755482 : ℝ)) (R := (0.778913524116 : ℝ)) (Q2 := (0.607394547182 : ℝ)) (T := (0.826909898570 : ℝ))
    (B := ((3424968260926057/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493404680133/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1711074647991931/2500000000000000) := by
  have hk1 : kappa q ≤ 0.604660829556 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493404680133 : ℝ)) (s := (0.869799874468 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606598260898 : ℝ) ≤ 0.682440005192 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606598260898 : ℝ)) (Q := (0.606598260898 : ℝ))
      (s := (0.795008521889 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777854015327 : ℝ)) (R := (0.778402783961 : ℝ)) (Q2 := (0.606598260898 : ℝ)) (T := (0.826567445537 : ℝ))
    (B := ((1711074647991931/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492209928341/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683866690203243/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603866542927 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492209928341 : ℝ)) (s := (0.870476528370 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605802512022 : ℝ) ≤ 0.681875057888 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605802512022 : ℝ)) (Q := (0.605802512022 : ℝ))
      (s := (0.795615055431 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777343284870 : ℝ)) (R := (0.777892053504 : ℝ)) (Q2 := (0.605802512022 : ℝ)) (T := (0.826225244223 : ℝ))
    (B := ((683866690203243/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (9820303531/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (106766272535021/156250000000000) := by
  have hk1 : kappa q ≤ 0.603072792511 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491015176550 : ℝ)) (s := (0.871151018135 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605007299976 : ℝ) ≤ 0.681310759159 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605007299976 : ℝ)) (Q := (0.605007299976 : ℝ))
      (s := (0.796219923750 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776832563759 : ℝ)) (R := (0.777381332393 : ℝ)) (Q2 := (0.605007299976 : ℝ)) (T := (0.825883294220 : ℝ))
    (B := ((106766272535021/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244910212379/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1365484440565237/2000000000000000) := by
  have hk1 : kappa q ≤ 0.602279577736 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489820424758 : ℝ)) (s := (0.871823348787 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604212624187 : ℝ) ≤ 0.680747107824 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604212624187 : ℝ)) (Q := (0.604212624187 : ℝ))
      (s := (0.796823132680 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776321851644 : ℝ)) (R := (0.776870620278 : ℝ)) (Q2 := (0.604212624187 : ℝ)) (T := (0.825541595125 : ℝ))
    (B := ((1365484440565237/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488625672967/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821809174055069/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601486898030 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488625672967 : ℝ)) (s := (0.872493525316 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603418484085 : ℝ) ≤ 0.680184102704 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603418484085 : ℝ)) (Q := (0.603418484085 : ℝ))
      (s := (0.797424688021 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775811148176 : ℝ)) (R := (0.776359916810 : ℝ)) (Q2 := (0.603418484085 : ℝ)) (T := (0.825200146532 : ℝ))
    (B := ((6821809174055069/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19497236847/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1704050586558073/2500000000000000) := by
  have hk1 : kappa q ≤ 0.600694752828 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487430921175 : ℝ)) (s := (0.873161552683 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602624879103 : ℝ) ≤ 0.679621742626 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602624879103 : ℝ)) (Q := (0.602624879103 : ℝ))
      (s := (0.798024595540 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775300453007 : ℝ)) (R := (0.775849221641 : ℝ)) (Q2 := (0.602624879103 : ℝ)) (T := (0.824858948043 : ℝ))
    (B := ((1704050586558073/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60779521173/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810601709698121/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599903141566 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486236169384 : ℝ)) (s := (0.873827435815 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601831808676 : ℝ) ≤ 0.679060026420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601831808676 : ℝ)) (Q := (0.601831808676 : ℝ))
      (s := (0.798622860972 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774789765789 : ℝ)) (R := (0.775338534423 : ℝ)) (Q2 := (0.601831808676 : ℝ)) (T := (0.824517999256 : ℝ))
    (B := ((6810601709698121/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60630177199/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (850625906853573/1250000000000000) := by
  have hk1 : kappa q ≤ 0.599112063683 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485041417592 : ℝ)) (s := (0.874491179613 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601039272240 : ℝ) ≤ 0.678498952918 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601039272240 : ℝ)) (Q := (0.601039272240 : ℝ))
      (s := (0.799219490019 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774279086175 : ℝ)) (R := (0.774827854809 : ℝ)) (Q2 := (0.601039272240 : ℝ)) (T := (0.824177299773 : ℝ))
    (B := ((850625906853573/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483846665801/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (106240921438051/156250000000000) := by
  have hk1 : kappa q ≤ 0.598321518622 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483846665801 : ℝ)) (s := (0.875152788943 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600247269239 : ℝ) ≤ 0.677938520962 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600247269239 : ℝ)) (Q := (0.600247269239 : ℝ))
      (s := (0.799814488348 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773768413821 : ℝ)) (R := (0.774317182455 : ℝ)) (Q2 := (0.600247269239 : ℝ)) (T := (0.823836849200 : ℝ))
    (B := ((106240921438051/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482651914009/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (679383685176509/1000000000000000) := by
  have hk1 : kappa q ≤ 0.597531505828 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482651914009 : ℝ)) (s := (0.875812268642 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599455799116 : ℝ) ≤ 0.677378729392 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599455799116 : ℝ)) (Q := (0.599455799116 : ℝ))
      (s := (0.800407861597 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773257748382 : ℝ)) (R := (0.773806517016 : ℝ)) (Q2 := (0.599455799116 : ℝ)) (T := (0.823496647139 : ℝ))
    (B := ((679383685176509/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240728581109/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (678826086745423/1000000000000000) := by
  have hk1 : kappa q ≤ 0.596742024751 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481457162218 : ℝ)) (s := (0.876469623518 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598664861320 : ℝ) ≤ 0.676819577057 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598664861320 : ℝ)) (Q := (0.598664861320 : ℝ))
      (s := (0.800999615369 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772747089516 : ℝ)) (R := (0.773295858150 : ℝ)) (Q2 := (0.598664861320 : ℝ)) (T := (0.823156693199 : ℝ))
    (B := ((678826086745423/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240131205213/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782689853898723/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595953074841 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480262410426 : ℝ)) (s := (0.877124858348 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597874455301 : ℝ) ≤ 0.676261062808 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597874455301 : ℝ)) (Q := (0.597874455301 : ℝ))
      (s := (0.801589755236 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772236436880 : ℝ)) (R := (0.772785205514 : ℝ)) (Q2 := (0.597874455301 : ℝ)) (T := (0.822816986988 : ℝ))
    (B := ((6782689853898723/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (95813531727/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (135542499520183/200000000000000) := by
  have hk1 : kappa q ≤ 0.595164655555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479067658635 : ℝ)) (s := (0.877777977880 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597084580515 : ℝ) ≤ 0.675703185502 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597084580515 : ℝ)) (Q := (0.597084580515 : ℝ))
      (s := (0.802178286737 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771725790135 : ℝ)) (R := (0.772274558769 : ℝ)) (Q2 := (0.597084580515 : ℝ)) (T := (0.822477528119 : ℝ))
    (B := ((135542499520183/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12625 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477872906843/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771566225388459/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594376766350 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477872906843 : ℝ)) (s := (0.878428986832 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596295236417 : ℝ) ≤ 0.675145943998 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596295236417 : ℝ)) (Q := (0.596295236417 : ℝ))
      (s := (0.802765215382 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771215148940 : ℝ)) (R := (0.771763917574 : ℝ)) (Q2 := (0.596295236417 : ℝ)) (T := (0.822138316202 : ℝ))
    (B := ((6771566225388459/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S11
namespace BstLean.Part269.S11
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12625 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052641668890 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S11.wn_upper (by omega : 12625 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010628574973 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035916364443)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010628574973 + 2 * 0.737676 / 12625) := by gcongr
    _ ≤ (0.052641668890 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12625 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12625 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.361025271221 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12625 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.361025271221 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12625 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003612287085 + 0.003313915228 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003612287085 + 0.003313915228 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.361025271221 ≤ R)
    (hB : (X + 0.052641668890 + R + 0.008506688079) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008506688079 := by
    convert (BstLean.Part269.S11.finite_centre_upper (by omega : 12625 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (85640421581/1000000000000)
  | 2 => (8658596251/100000000000)
  | 3 => (10941256949/125000000000)
  | 4 => (88474213539/1000000000000)
  | 5 => (89420262867/1000000000000)
  | 6 => (90370390089/1000000000000)
  | 7 => (4566359609/50000000000)
  | 8 => (92293731337/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003612287085 + 0.003313915228 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219320478699 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010999076198 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003612287085 + 0.003313915228 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220889825458 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011114384464 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003612287085 + 0.003313915228 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222438707522 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011229311876 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003612287085 + 0.003313915228 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223967332324 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011343866783 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003612287085 + 0.003313915228 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225475902120 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011458057296 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003612287085 + 0.003313915228 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226964612500 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011571891173 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003612287085 + 0.003313915228 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228433654257 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011685375963 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12625 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003612287085 + 0.003313915228 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229883211930 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011798518890 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12625 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g) :
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

end BstLean.Part269.S11

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S13
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12675 ≤ n) : wn n ≤ 1.035844829189 := by
  have hnR : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.583302491977 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.583302491977 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035844829189 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12675 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12675 + 24 / (12675 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12675 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008489820724 : ℝ) := by
  have hnR : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.583302491977 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12675 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035844829189 * (81 / 1000 / 12675)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035844829189 * n *
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
        4 * (1 / 2.506628) * 1.035844829189 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035844829189 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035844829189 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12675)) / 112.583302491977 := by gcongr
    _ ≤ (0.008489820724 : ℝ) := by norm_num

end BstLean.Part269.S13
namespace BstLean.Part269.S13
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12675 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12675 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12675 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12675 + 0.008489820724 / 112.583302491977) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12675 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12675 := by gcongr
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
  have hn : (112.583302491977 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S13.finite_centre_upper (by omega : 12675 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (132014462541/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010272501214081/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627934723123 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528057850164 : ℝ)) (s := (0.849208400147 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629909836916 : ℝ) ≤ 0.699110101101 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629909836916 : ℝ)) (Q := (0.629909836916 : ℝ))
      (s := (0.776668267253 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792672189774 : ℝ)) (R := (0.793218793640 : ℝ)) (Q2 := (0.629909836916 : ℝ)) (T := (0.836601899443 : ℝ))
    (B := ((7010272501214081/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (26343181759/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (175111460187231/250000000000000) := by
  have hk1 : kappa q ≤ 0.627124984419 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526863635180 : ℝ)) (s := (0.849949827887 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629098620429 : ℝ) ≤ 0.698526074145 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629098620429 : ℝ)) (Q := (0.629098620429 : ℝ))
      (s := (0.777325495385 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792161259932 : ℝ)) (R := (0.792707863798 : ℝ)) (Q2 := (0.629098620429 : ℝ)) (T := (0.836252383577 : ℝ))
    (B := ((175111460187231/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131417355049/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499325419049711/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626315799408 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525669420196 : ℝ)) (s := (0.850688932966 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628287958286 : ℝ) ≤ 0.697942731291 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628287958286 : ℝ)) (Q := (0.628287958286 : ℝ))
      (s := (0.777980874748 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791650350045 : ℝ)) (R := (0.792196953911 : ℝ)) (Q2 := (0.628287958286 : ℝ)) (T := (0.835903131231 : ℝ))
    (B := ((3499325419049711/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524475205213/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1398569956426893/2000000000000000) := by
  have hk1 : kappa q ≤ 0.625507167426 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524475205213 : ℝ)) (s := (0.851425721433 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477849821 : ℝ) ≤ 0.697360071237 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477849821 : ℝ)) (Q := (0.627477849821 : ℝ))
      (s := (0.778634412279 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791139459732 : ℝ)) (R := (0.791686063598 : ℝ)) (Q2 := (0.627477849821 : ℝ)) (T := (0.835554141956 : ℝ))
    (B := ((1398569956426893/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523280990229/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987055228727559/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624699087813 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523280990229 : ℝ)) (s := (0.852160199297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668294371 : ℝ) ≤ 0.696778092682 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668294371 : ℝ)) (Q := (0.626668294371 : ℝ))
      (s := (0.779286114871 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790628588612 : ℝ)) (R := (0.791175192478 : ℝ)) (Q2 := (0.626668294371 : ℝ)) (T := (0.835205415301 : ℝ))
    (B := ((6987055228727559/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (104417355049/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1745316791763743/2500000000000000) := by
  have hk1 : kappa q ≤ 0.623891559914 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522086775245 : ℝ)) (s := (0.852892372527 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859291282 : ℝ) ≤ 0.696196794334 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859291282 : ℝ)) (Q := (0.625859291282 : ℝ))
      (s := (0.779935989371 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790117736310 : ℝ)) (R := (0.790664340176 : ℝ)) (Q2 := (0.625859291282 : ℝ)) (T := (0.834856950822 : ℝ))
    (B := ((1745316791763743/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520892560261/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3487742793167891/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623084583075 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520892560261 : ℝ)) (s := (0.853622247054 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625050839900 : ℝ) ≤ 0.695616174905 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625050839900 : ℝ)) (Q := (0.625050839900 : ℝ))
      (s := (0.780584042587 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789606902448 : ℝ)) (R := (0.790153506314 : ℝ)) (Q2 := (0.625050839900 : ℝ)) (T := (0.834508748074 : ℝ))
    (B := ((3487742793167891/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259849172639/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742427618957901/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622278156647 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519698345278 : ℝ)) (s := (0.854349828768 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624242939571 : ℝ) ≤ 0.695036233104 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624242939571 : ℝ)) (Q := (0.624242939571 : ℝ))
      (s := (0.781230281285 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789096086649 : ℝ)) (R := (0.789642690515 : ℝ)) (Q2 := (0.624242939571 : ℝ)) (T := (0.834160806611 : ℝ))
    (B := ((1742427618957901/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259252065147/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (870492728105791/1250000000000000) := by
  have hk1 : kappa q ≤ 0.621472279982 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518504130294 : ℝ)) (s := (0.855075123524 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623435589650 : ℝ) ≤ 0.694456967653 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623435589650 : ℝ)) (Q := (0.623435589650 : ℝ))
      (s := (0.781874712188 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788585288539 : ℝ)) (R := (0.789131892405 : ℝ)) (Q2 := (0.623435589650 : ℝ)) (T := (0.833813125991 : ℝ))
    (B := ((870492728105791/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51730991531/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958179622725857/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620666952437 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517309915310 : ℝ)) (s := (0.855798137134 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622628789490 : ℝ) ≤ 0.693878377273 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622628789490 : ℝ)) (Q := (0.622628789490 : ℝ))
      (s := (0.782517341980 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788074507744 : ℝ)) (R := (0.788621111610 : ℝ)) (Q2 := (0.622628789490 : ℝ)) (T := (0.833465705773 : ℝ))
    (B := ((6958179622725857/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516115700327/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (86905298235723/125000000000000) := by
  have hk1 : kappa q ≤ 0.619862173371 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516115700327 : ℝ)) (s := (0.856518875377 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621822538450 : ℝ) ≤ 0.693300460690 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621822538450 : ℝ)) (Q := (0.621822538450 : ℝ))
      (s := (0.783158177303 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787563743890 : ℝ)) (R := (0.788110347756 : ℝ)) (Q2 := (0.621822538450 : ℝ)) (T := (0.833118545519 : ℝ))
    (B := ((86905298235723/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514921485343/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473337261335711/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619057942145 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514921485343 : ℝ)) (s := (0.857237343991 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621016835889 : ℝ) ≤ 0.692723216632 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621016835889 : ℝ)) (Q := (0.621016835889 : ℝ))
      (s := (0.783797224761 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787052996604 : ℝ)) (R := (0.787599600470 : ℝ)) (Q2 := (0.621016835889 : ℝ)) (T := (0.832771644787 : ℝ))
    (B := ((3473337261335711/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513727270359/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940931603636979/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618254258126 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513727270359 : ℝ)) (s := (0.857953548679 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620211681174 : ℝ) ≤ 0.692146643837 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620211681174 : ℝ)) (Q := (0.620211681174 : ℝ))
      (s := (0.784434490914 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786542265517 : ℝ)) (R := (0.787088869383 : ℝ)) (Q2 := (0.620211681174 : ℝ)) (T := (0.832425003144 : ℝ))
    (B := ((6940931603636979/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32033315961/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935195091265869/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617451120682 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512533055376 : ℝ)) (s := (0.858667495104 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619407073671 : ℝ) ≤ 0.691570741041 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619407073671 : ℝ)) (Q := (0.619407073671 : ℝ))
      (s := (0.785069982286 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786031550258 : ℝ)) (R := (0.786578154124 : ℝ)) (Q2 := (0.619407073671 : ℝ)) (T := (0.832078620154 : ℝ))
    (B := ((6935195091265869/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63917355049/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929464975110181/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616648529184 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511338840392 : ℝ)) (s := (0.859379188896 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618603012750 : ℝ) ≤ 0.690995506987 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618603012750 : ℝ)) (Q := (0.618603012750 : ℝ))
      (s := (0.785703705361 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785520850457 : ℝ)) (R := (0.786067454323 : ℝ)) (Q2 := (0.618603012750 : ℝ)) (T := (0.831732495382 : ℝ))
    (B := ((6929464975110181/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1992752443/3906250000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (86546765559531/125000000000000) := by
  have hk1 : kappa q ≤ 0.615846483008 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510144625408 : ℝ)) (s := (0.860088635646 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617799497786 : ℝ) ≤ 0.690420940423 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617799497786 : ℝ)) (Q := (0.617799497786 : ℝ))
      (s := (0.786335666580 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785010165747 : ℝ)) (R := (0.785556769613 : ℝ)) (Q2 := (0.617799497786 : ℝ)) (T := (0.831386628397 : ℝ))
    (B := ((86546765559531/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20358016417/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918023889855563/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615044981531 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508950410425 : ℝ)) (s := (0.860795840911 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616996528156 : ℝ) ≤ 0.689847040099 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616996528156 : ℝ)) (Q := (0.616996528156 : ℝ))
      (s := (0.786965872350 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784499495761 : ℝ)) (R := (0.785046099627 : ℝ)) (Q2 := (0.616996528156 : ℝ)) (T := (0.831041018769 : ℝ))
    (B := ((6918023889855563/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507756195441/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1382462580012443/2000000000000000) := by
  have hk1 : kappa q ≤ 0.614244024133 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507756195441 : ℝ)) (s := (0.861500810210 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616194103238 : ℝ) ≤ 0.689273804770 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616194103238 : ℝ)) (Q := (0.616194103238 : ℝ))
      (s := (0.787594329040 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783988840132 : ℝ)) (R := (0.784535443998 : ℝ)) (Q2 := (0.616194103238 : ℝ)) (T := (0.830695666069 : ℝ))
    (B := ((1382462580012443/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506561980457/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906608265094961/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613443610200 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506561980457 : ℝ)) (s := (0.862203549028 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615392222416 : ℝ) ≤ 0.688701233195 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615392222416 : ℝ)) (Q := (0.615392222416 : ℝ))
      (s := (0.788221042976 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783478198496 : ℝ)) (R := (0.784024802362 : ℝ)) (Q2 := (0.615392222416 : ℝ)) (T := (0.830350569868 : ℝ))
    (B := ((6906608265094961/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505367765473/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (690090997470583/1000000000000000) := by
  have hk1 : kappa q ≤ 0.612643739117 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505367765473 : ℝ)) (s := (0.862904062814 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614590885076 : ℝ) ≤ 0.688129324139 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614590885076 : ℝ)) (Q := (0.614590885076 : ℝ))
      (s := (0.788846020452 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782967570488 : ℝ)) (R := (0.783514174354 : ℝ)) (Q2 := (0.614590885076 : ℝ)) (T := (0.830005729742 : ℝ))
    (B := ((690090997470583/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50417355049/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (689521801868611/1000000000000000) := by
  have hk1 : kappa q ≤ 0.611844410277 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504173550490 : ℝ)) (s := (0.863602356983 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613790090607 : ℝ) ≤ 0.687558076368 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613790090607 : ℝ)) (Q := (0.613790090607 : ℝ))
      (s := (0.789469267719 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782456955746 : ℝ)) (R := (0.783003559612 : ℝ)) (Q2 := (0.613790090607 : ℝ)) (T := (0.829661145266 : ℝ))
    (B := ((689521801868611/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (251489667753/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444766193433059/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611045623072 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502979335506 : ℝ)) (s := (0.864298436916 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612989838402 : ℝ) ≤ 0.686987488655 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612989838402 : ℝ)) (Q := (0.612989838402 : ℝ))
      (s := (0.790090790996 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781946353908 : ℝ)) (R := (0.782492957774 : ℝ)) (Q2 := (0.612989838402 : ℝ)) (T := (0.829316816018 : ℝ))
    (B := ((3444766193433059/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250892560261/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883853069114957/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610247376898 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501785120522 : ℝ)) (s := (0.864992307956 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612190127856 : ℝ) ≤ 0.686417559776 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612190127856 : ℝ)) (Q := (0.612190127856 : ℝ))
      (s := (0.790710596461 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781435764613 : ℝ)) (R := (0.781982368479 : ℝ)) (Q2 := (0.612190127856 : ℝ)) (T := (0.828972741577 : ℝ))
    (B := ((6883853069114957/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500590905539/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (687818005534029/1000000000000000) := by
  have hk1 : kappa q ≤ 0.609449671156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500590905539 : ℝ)) (s := (0.865683975416 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611390958369 : ℝ) ≤ 0.685848288512 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611390958369 : ℝ)) (Q := (0.611390958369 : ℝ))
      (s := (0.791328690258 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780925187502 : ℝ)) (R := (0.781471791368 : ℝ)) (Q2 := (0.611390958369 : ℝ)) (T := (0.828628921524 : ℝ))
    (B := ((687818005534029/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99879338111/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1374502667097621/2000000000000000) := by
  have hk1 : kappa q ≤ 0.608652505247 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499396690555 : ℝ)) (s := (0.866373444574 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610592329339 : ℝ) ≤ 0.685279673645 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610592329339 : ℝ)) (Q := (0.610592329339 : ℝ))
      (s := (0.791945078495 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780414622214 : ℝ)) (R := (0.780961226080 : ℝ)) (Q2 := (0.610592329339 : ℝ)) (T := (0.828285355439 : ℝ))
    (B := ((1374502667097621/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498202475571/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433426449771243/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607855878579 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498202475571 : ℝ)) (s := (0.867060720674 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609794240175 : ℝ) ≤ 0.684711713967 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609794240175 : ℝ)) (Q := (0.609794240175 : ℝ))
      (s := (0.792559767242 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779904068394 : ℝ)) (R := (0.780450672260 : ℝ)) (Q2 := (0.609794240175 : ℝ)) (T := (0.827942042908 : ℝ))
    (B := ((3433426449771243/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (124252065147/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430599368762693/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607059790560 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497008260588 : ℝ)) (s := (0.867745808926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608996690283 : ℝ) ≤ 0.684144408270 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608996690283 : ℝ)) (Q := (0.608996690283 : ℝ))
      (s := (0.793172762534 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779393525684 : ℝ)) (R := (0.779940129550 : ℝ)) (Q2 := (0.608996690283 : ℝ)) (T := (0.827598983517 : ℝ))
    (B := ((3430599368762693/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123953511401/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1371110167899281/2000000000000000) := by
  have hk1 : kappa q ≤ 0.606264240602 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495814045604 : ℝ)) (s := (0.868428714508 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608199679074 : ℝ) ≤ 0.683577755351 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608199679074 : ℝ)) (Q := (0.608199679074 : ℝ))
      (s := (0.793784070371 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778882993729 : ℝ)) (R := (0.779429597595 : ℝ)) (Q2 := (0.608199679074 : ℝ)) (T := (0.827256176852 : ℝ))
    (B := ((1371110167899281/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24730991531/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (85623864944407/125000000000000) := by
  have hk1 : kappa q ≤ 0.605469228122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494619830620 : ℝ)) (s := (0.869109442567 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607403205964 : ℝ) ≤ 0.683011754013 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607403205964 : ℝ)) (Q := (0.607403205964 : ℝ))
      (s := (0.794393696718 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778372472175 : ℝ)) (R := (0.778919076041 : ℝ)) (Q2 := (0.607403205964 : ℝ)) (T := (0.826913622503 : ℝ))
    (B := ((85623864944407/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493425615637/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844273795828069/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604674752536 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493425615637 : ℝ)) (s := (0.869787998212 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606607270369 : ℝ) ≤ 0.682446403061 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606607270369 : ℝ)) (Q := (0.606607270369 : ℝ))
      (s := (0.795001647505 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777861960668 : ℝ)) (R := (0.778408564534 : ℝ)) (Q2 := (0.606607270369 : ℝ)) (T := (0.826571320059 : ℝ))
    (B := ((6844273795828069/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492231400653/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838644630494131/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603880813267 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492231400653 : ℝ)) (s := (0.870464386527 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605811871710 : ℝ) ≤ 0.681881701305 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605811871710 : ℝ)) (Q := (0.605811871710 : ℝ))
      (s := (0.795607928628 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777351458856 : ℝ)) (R := (0.777898062722 : ℝ)) (Q2 := (0.605811871710 : ℝ)) (T := (0.826229269114 : ℝ))
    (B := ((6838644630494131/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491037185669/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416510844879353/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603087409740 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491037185669 : ℝ)) (s := (0.871138612559 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605017009410 : ℝ) ≤ 0.681317647560 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605017009410 : ℝ)) (Q := (0.605017009410 : ℝ))
      (s := (0.796212545948 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776840966388 : ℝ)) (R := (0.777387570254 : ℝ)) (Q2 := (0.605017009410 : ℝ)) (T := (0.825887469262 : ℝ))
    (B := ((3416510844879353/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97968594137/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413702481933149/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602294541381 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489842970685 : ℝ)) (s := (0.871810681324 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604222682896 : ℝ) ≤ 0.680754240646 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604222682896 : ℝ)) (Q := (0.604222682896 : ℝ))
      (s := (0.796815505293 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776330482913 : ℝ)) (R := (0.776877086779 : ℝ)) (Q2 := (0.604222682896 : ℝ)) (T := (0.825545920098 : ℝ))
    (B := ((3413702481933149/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244324377851/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364358888619549/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601502207623 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488648755702 : ℝ)) (s := (0.872480597808 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603428891598 : ℝ) ≤ 0.680191479383 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603428891598 : ℝ)) (Q := (0.603428891598 : ℝ))
      (s := (0.797416812455 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775820008083 : ℝ)) (R := (0.776366611949 : ℝ)) (Q2 := (0.603428891598 : ℝ)) (T := (0.825204621218 : ℝ))
    (B := ((1364358888619549/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243727270359/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816190117770003/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600710407899 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487454540718 : ℝ)) (s := (0.873148366965 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602635634948 : ℝ) ≤ 0.679629362600 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602635634948 : ℝ)) (Q := (0.602635634948 : ℝ))
      (s := (0.798016473196 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775309541549 : ℝ)) (R := (0.775856145415 : ℝ)) (Q2 := (0.602635634948 : ℝ)) (T := (0.824863572222 : ℝ))
    (B := ((6816190117770003/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243130162867/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810591978235937/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599919141646 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486260325734 : ℝ)) (s := (0.873813993718 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601842912386 : ℝ) ≤ 0.679067889131 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601842912386 : ℝ)) (Q := (0.601842912386 : ℝ))
      (s := (0.798614493239 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774799082966 : ℝ)) (R := (0.775345686832 : ℝ)) (Q2 := (0.601842912386 : ℝ)) (T := (0.824522772714 : ℝ))
    (B := ((6810591978235937/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485066110751/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (425312500930257/625000000000000) := by
  have hk1 : kappa q ≤ 0.599128408305 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485066110751 : ℝ)) (s := (0.874477482959 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601050723345 : ℝ) ≤ 0.678507057808 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601050723345 : ℝ)) (Q := (0.601050723345 : ℝ))
      (s := (0.799210878284 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774288631986 : ℝ)) (R := (0.774835235852 : ℝ)) (Q2 := (0.601050723345 : ℝ)) (T := (0.824182222291 : ℝ))
    (B := ((425312500930257/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483871895767/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399707109069293/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598338207318 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483871895767 : ℝ)) (s := (0.875138839549 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600259067273 : ℝ) ≤ 0.677946867474 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600259067273 : ℝ)) (Q := (0.600259067273 : ℝ))
      (s := (0.799805633987 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773778188266 : ℝ)) (R := (0.774324792132 : ℝ)) (Q2 := (0.600259067273 : ℝ)) (T := (0.823841920561 : ℝ))
    (B := ((3399707109069293/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482677680783/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3396917289229351/5000000000000000) := by
  have hk1 : kappa q ≤ 0.597548538132 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482677680783 : ℝ)) (s := (0.875798068321 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599467943612 : ℝ) ≤ 0.677387316973 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599467943612 : ℝ)) (Q := (0.599467943612 : ℝ))
      (s := (0.800398765980 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773267751462 : ℝ)) (R := (0.773814355328 : ℝ)) (Q2 := (0.599467943612 : ℝ)) (T := (0.823501867130 : ℝ))
    (B := ((3396917289229351/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2407417329/5000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788260961214487/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596759400197 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481483465800 : ℝ)) (s := (0.876455174075 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598677351811 : ℝ) ≤ 0.676828405152 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598677351811 : ℝ)) (Q := (0.598677351811 : ℝ))
      (s := (0.800990279859 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772757321230 : ℝ)) (R := (0.773303925096 : ℝ)) (Q2 := (0.598677351811 : ℝ)) (T := (0.823162061603 : ℝ))
    (B := ((6788260961214487/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (938064943/1953125000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (339134621180187/500000000000000) := by
  have hk1 : kappa q ≤ 0.595970792965 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480289250816 : ℝ)) (s := (0.877110161583 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597887291322 : ℝ) ≤ 0.676270130865 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597887291322 : ℝ)) (Q := (0.597887291322 : ℝ))
      (s := (0.801580181190 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772246897231 : ℝ)) (R := (0.772793501097 : ℝ)) (Q2 := (0.597887291322 : ℝ)) (T := (0.822822503590 : ℝ))
    (B := ((339134621180187/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (59886879479/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777130017243857/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595182715890 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479095035832 : ℝ)) (s := (0.877763035586 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597097761599 : ℝ) ≤ 0.675712492970 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597097761599 : ℝ)) (Q := (0.597097761599 : ℝ))
      (s := (0.802168475505 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771736479122 : ℝ)) (R := (0.772283082988 : ℝ)) (Q2 := (0.597097761599 : ℝ)) (T := (0.822483192704 : ℝ))
    (B := ((6777130017243857/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12675 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477900820849/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385786866363737/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594395168434 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477900820849 : ℝ)) (s := (0.878413800798 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596308762102 : ℝ) ≤ 0.675155490329 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596308762102 : ℝ)) (Q := (0.596308762102 : ℝ))
      (s := (0.802755168305 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771226066567 : ℝ)) (R := (0.771772670433 : ℝ)) (Q2 := (0.596308762102 : ℝ)) (T := (0.822144128558 : ℝ))
    (B := ((3385786866363737/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S13
namespace BstLean.Part269.S13
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12675 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052536608508 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S13.wn_upper (by omega : 12675 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010607590599 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035844829189)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010607590599 + 2 * 0.737676 / 12675) := by gcongr
    _ ≤ (0.052536608508 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12675 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12675 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.583302491977 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12675 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.583302491977 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12675 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003538895953 + 0.003300387184 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003538895953 + 0.003300387184 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.583302491977 ≤ R)
    (hB : (X + 0.052536608508 + R + 0.008489820724) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008489820724 := by
    convert (BstLean.Part269.S13.finite_centre_upper (by omega : 12675 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (10686646631/125000000000)
  | 2 => (86435975913/1000000000000)
  | 3 => (87376926229/1000000000000)
  | 4 => (44158721929/500000000000)
  | 5 => (44629623071/500000000000)
  | 6 => (90204392081/1000000000000)
  | 7 => (11394416333/125000000000)
  | 8 => (92114953401/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003538895953 + 0.003300387184 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219138457674 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010977360330 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003538895953 + 0.003300387184 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220708878140 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011092440939 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003538895953 + 0.003300387184 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222258802180 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011207141446 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003538895953 + 0.003300387184 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223788438339 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011321470183 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003538895953 + 0.003300387184 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225297989931 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011435435245 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003538895953 + 0.003300387184 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226787653546 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011549044376 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003538895953 + 0.003300387184 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228257620934 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011662305109 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12675 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003538895953 + 0.003300387184 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229708077543 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011775224654 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12675 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g) :
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

end BstLean.Part269.S13

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S4
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12450 ≤ n) : wn n ≤ 1.036170142337 := by
  have hnR : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.579568022106 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.579568022106 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036170142337 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12450 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12450 + 24 / (12450 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12450 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008566524203 : ℝ) := by
  have hnR : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.579568022106 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12450 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036170142337 * (81 / 1000 / 12450)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036170142337 * n *
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
        4 * (1 / 2.506628) * 1.036170142337 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036170142337 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036170142337 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12450)) / 111.579568022106 := by gcongr
    _ ≤ (0.008566524203 : ℝ) := by norm_num

end BstLean.Part269.S4
namespace BstLean.Part269.S4
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12450 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12450 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12450 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12450 + 0.008566524203 / 111.579568022106) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12450 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12450 := by gcongr
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
  have hn : (111.579568022106 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S4.finite_centre_upper (by omega : 12450 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528033435071/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3505365708144531/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627918162895 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528033435071 : ℝ)) (s := (0.849223581543 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629916077783 : ℝ) ≤ 0.699114595255 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629916077783 : ℝ)) (Q := (0.629916077783 : ℝ))
      (s := (0.776663205612 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792666240811 : ℝ)) (R := (0.793222723060 : ℝ)) (Q2 := (0.629916077783 : ℝ)) (T := (0.836604588442 : ℝ))
    (B := ((3505365708144531/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263418389289/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (140098101596959/200000000000000) := by
  have hk1 : kappa q ≤ 0.627106780641 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526836778578 : ℝ)) (s := (0.849966475067 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629103204616 : ℝ) ≤ 0.698529373681 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629103204616 : ℝ)) (Q := (0.629103204616 : ℝ))
      (s := (0.777321785326 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792154269740 : ℝ)) (R := (0.792710751989 : ℝ)) (Q2 := (0.629103204616 : ℝ)) (T := (0.836254358622 : ℝ))
    (B := ((140098101596959/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105128024417/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499542647405029/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626295954330 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525640122085 : ℝ)) (s := (0.850707036562 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628290888045 : ℝ) ≤ 0.697944838998 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628290888045 : ℝ)) (Q := (0.628290888045 : ℝ))
      (s := (0.777978508701 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791642318700 : ℝ)) (R := (0.792198800949 : ℝ)) (Q2 := (0.628290888045 : ℝ)) (T := (0.835904393396 : ℝ))
    (B := ((3499542647405029/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65555433199/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1748318012549417/2500000000000000) := by
  have hk1 : kappa q ≤ 0.625485683296 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524443465592 : ℝ)) (s := (0.851445272110 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627479127403 : ℝ) ≤ 0.697360989898 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627479127403 : ℝ)) (Q := (0.627479127403 : ℝ))
      (s := (0.778633382713 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791130387308 : ℝ)) (R := (0.791686869557 : ℝ)) (Q2 := (0.627479127403 : ℝ)) (T := (0.835554692310 : ℝ))
    (B := ((1748318012549417/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523246809099/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3493732667538383/5000000000000000) := by
  have hk1 : kappa q ≤ 0.624675966874 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523246809099 : ℝ)) (s := (0.852181187758 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667922024 : ℝ) ≤ 0.696777825072 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667922024 : ℝ)) (Q := (0.626667922024 : ℝ))
      (s := (0.779286414296 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790618475183 : ℝ)) (R := (0.791174957432 : ℝ)) (Q2 := (0.626667922024 : ℝ)) (T := (0.835205254914 : ℝ))
    (B := ((3493732667538383/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261025076303/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (279266605542271/400000000000000) := by
  have hk1 : kappa q ≤ 0.623866804406 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522050152606 : ℝ)) (s := (0.852914789510 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625857271248 : ℝ) ≤ 0.696195343220 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625857271248 : ℝ)) (Q := (0.625857271248 : ℝ))
      (s := (0.779937610343 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790106581945 : ℝ)) (R := (0.790663064194 : ℝ)) (Q2 := (0.625857271248 : ℝ)) (T := (0.834856080757 : ℝ))
    (B := ((279266605542271/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520853496113/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975871449790273/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623058195233 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520853496113 : ℝ)) (s := (0.853646083332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625047174414 : ℝ) ≤ 0.695613543042 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625047174414 : ℝ)) (Q := (0.625047174414 : ℝ))
      (s := (0.780586977702 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789594707213 : ℝ)) (R := (0.790151189462 : ℝ)) (Q2 := (0.625047174414 : ℝ)) (T := (0.834507169391 : ℝ))
    (B := ((6975871449790273/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25982841981/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (697008425797273/1000000000000000) := by
  have hk1 : kappa q ≤ 0.622250138703 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519656839620 : ℝ)) (s := (0.854375075150 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624237630873 : ℝ) ≤ 0.695032423249 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624237630873 : ℝ)) (Q := (0.624237630873 : ℝ))
      (s := (0.781234523177 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789082850612 : ℝ)) (R := (0.789639332861 : ℝ)) (Q2 := (0.624237630873 : ℝ)) (T := (0.834158520373 : ℝ))
    (B := ((697008425797273/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518460183127/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392860710468447/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621442634163 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518460183127 : ℝ)) (s := (0.855101770851 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623428639966 : ℝ) ≤ 0.694451982545 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623428639966 : ℝ)) (Q := (0.623428639966 : ℝ))
      (s := (0.781880253537 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788571011761 : ℝ)) (R := (0.789127494010 : ℝ)) (Q2 := (0.623428639966 : ℝ)) (T := (0.833810133253 : ℝ))
    (B := ((1392860710468447/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258631763317/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (217454041318101/312500000000000) := by
  have hk1 : kappa q ≤ 0.620635680967 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517263526634 : ℝ)) (s := (0.855826176285 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622620201049 : ℝ) ≤ 0.693872219648 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622620201049 : ℝ)) (Q := (0.622620201049 : ℝ))
      (s := (0.782524175503 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788059190286 : ℝ)) (R := (0.788615672535 : ℝ)) (Q2 := (0.622620201049 : ℝ)) (T := (0.833462007589 : ℝ))
    (B := ((217454041318101/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516066870141/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952761556806253/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619829278470 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516066870141 : ℝ)) (s := (0.856548297263 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621812313473 : ℝ) ≤ 0.693293133275 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621812313473 : ℝ)) (Q := (0.621812313473 : ℝ))
      (s := (0.783166295760 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787547385810 : ℝ)) (R := (0.788103868059 : ℝ)) (Q2 := (0.621812313473 : ℝ)) (T := (0.833114142939 : ℝ))
    (B := ((6952761556806253/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32179388353/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6947000245587663/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619023426030 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514870213648 : ℝ)) (s := (0.857268139557 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621004976598 : ℝ) ≤ 0.692714722150 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621004976598 : ℝ)) (Q := (0.621004976598 : ℝ))
      (s := (0.783806620948 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787035597960 : ℝ)) (R := (0.787592080209 : ℝ)) (Q2 := (0.621004976598 : ℝ)) (T := (0.832766538862 : ℝ))
    (B := ((6947000245587663/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128418389289/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1388249075585879/2000000000000000) := by
  have hk1 : kappa q ≤ 0.618218123009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513673557156 : ℝ)) (s := (0.857985708902 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620198189782 : ℝ) ≤ 0.692136984998 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620198189782 : ℝ)) (Q := (0.620198189782 : ℝ))
      (s := (0.784445157670 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786523826362 : ℝ)) (R := (0.787080308611 : ℝ)) (Q2 := (0.620198189782 : ℝ)) (T := (0.832419194919 : ℝ))
    (B := ((1388249075585879/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512476900663/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935496943278697/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617413368772 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512476900663 : ℝ)) (s := (0.858701010997 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619391952392 : ℝ) ≤ 0.691559920552 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619391952392 : ℝ)) (Q := (0.619391952392 : ℝ))
      (s := (0.785081912486 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786012070644 : ℝ)) (R := (0.786568552893 : ℝ)) (Q2 := (0.619391952392 : ℝ)) (T := (0.832072110673 : ℝ))
    (B := ((6935496943278697/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51128024417/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (55438039448991/80000000000000) := by
  have hk1 : kappa q ≤ 0.616609162686 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511280244170 : ℝ)) (s := (0.859414051504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618586263791 : ℝ) ≤ 0.690983527545 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618586263791 : ℝ)) (Q := (0.618586263791 : ℝ))
      (s := (0.785716891921 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785500330434 : ℝ)) (R := (0.786056812683 : ℝ)) (Q2 := (0.618586263791 : ℝ)) (T := (0.831725285686 : ℝ))
    (B := ((55438039448991/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510083587677/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1731004832748511/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615805504122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510083587677 : ℝ)) (s := (0.860124836046 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617781123350 : ℝ) ≤ 0.690407804716 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617781123350 : ℝ)) (Q := (0.617781123350 : ℝ))
      (s := (0.786350102456 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784988605362 : ℝ)) (R := (0.785545087611 : ℝ)) (Q2 := (0.617781123350 : ℝ)) (T := (0.831378719524 : ℝ))
    (B := ((1731004832748511/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31805433199/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (864786266557359/1250000000000000) := by
  have hk1 : kappa q ≤ 0.615002392455 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508886931184 : ℝ)) (s := (0.860833370212 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616976530444 : ℝ) ≤ 0.689832750811 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616976530444 : ℝ)) (Q := (0.616976530444 : ℝ))
      (s := (0.786981550535 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784476895059 : ℝ)) (R := (0.785033377308 : ℝ)) (Q2 := (0.616976530444 : ℝ)) (T := (0.831032411755 : ℝ))
    (B := ((864786266557359/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507690274691/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (345628366256417/500000000000000) := by
  have hk1 : kappa q ≤ 0.614199827062 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507690274691 : ℝ)) (s := (0.861539659554 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616172484446 : ℝ) ≤ 0.689258364574 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616172484446 : ℝ)) (Q := (0.616172484446 : ℝ))
      (s := (0.787611242564 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783965199156 : ℝ)) (R := (0.784521681405 : ℝ)) (Q2 := (0.616172484446 : ℝ)) (T := (0.830686361946 : ℝ))
    (B := ((345628366256417/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253246809099/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (690685089865249/1000000000000000) := by
  have hk1 : kappa q ≤ 0.613397807324 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506493618198 : ℝ)) (s := (0.862243709589 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615368984740 : ℝ) ≤ 0.688684644761 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615368984740 : ℝ)) (Q := (0.615368984740 : ℝ))
      (s := (0.788239184906 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783453517288 : ℝ)) (R := (0.784009999537 : ℝ)) (Q2 := (0.615368984740 : ℝ)) (T := (0.830340569669 : ℝ))
    (B := ((690685089865249/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (101059392341/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450570421360591/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612596332624 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505296961705 : ℝ)) (s := (0.862945525797 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614566030703 : ℝ) ≤ 0.688111590125 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614566030703 : ℝ)) (Q := (0.614566030703 : ℝ))
      (s := (0.788865383894 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782941849086 : ℝ)) (R := (0.783498331335 : ℝ)) (Q2 := (0.614566030703 : ℝ)) (T := (0.829995034494 : ℝ))
    (B := ((3450570421360591/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126025076303/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (430964821691491/625000000000000) := by
  have hk1 : kappa q ≤ 0.611795402349 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504100305212 : ℝ)) (s := (0.863645113624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613763621725 : ℝ) ≤ 0.687539199428 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613763621725 : ℝ)) (Q := (0.613763621725 : ℝ))
      (s := (0.789489845817 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782430194187 : ℝ)) (R := (0.782986676436 : ℝ)) (Q2 := (0.613763621725 : ℝ)) (T := (0.829649755995 : ℝ))
    (B := ((430964821691491/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502903648719/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889739801449291/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610995015888 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502903648719 : ℝ)) (s := (0.864342478481 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612961757192 : ℝ) ≤ 0.686967471433 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612961757192 : ℝ)) (Q := (0.612961757192 : ℝ))
      (s := (0.790112576929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781918552226 : ℝ)) (R := (0.782475034475 : ℝ)) (Q2 := (0.612961757192 : ℝ)) (T := (0.829304733746 : ℝ))
    (B := ((6889739801449291/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250853496113/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1721012198921341/2500000000000000) := by
  have hk1 : kappa q ≤ 0.610195172635 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501706992226 : ℝ)) (s := (0.865037625744 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612160436496 : ℝ) ≤ 0.686396404909 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612160436496 : ℝ)) (Q := (0.612160436496 : ℝ))
      (s := (0.790733583446 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781406922839 : ℝ)) (R := (0.781963405088 : ℝ)) (Q2 := (0.612160436496 : ℝ)) (T := (0.828959967324 : ℝ))
    (B := ((1721012198921341/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500510335733/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878364119618819/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609395871986 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500510335733 : ℝ)) (s := (0.865730560755 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611359659035 : ℝ) ≤ 0.685825998632 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611359659035 : ℝ)) (Q := (0.611359659035 : ℝ))
      (s := (0.791352871547 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780895305667 : ℝ)) (R := (0.781451787916 : ℝ)) (Q2 := (0.611359659035 : ℝ)) (T := (0.828615456309 : ℝ))
    (B := ((6878364119618819/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12482841981/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872685763135033/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608597113340 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499313679240 : ℝ)) (s := (0.866421288822 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610559424204 : ℝ) ≤ 0.685256251376 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610559424204 : ℝ)) (Q := (0.610559424204 : ℝ))
      (s := (0.791970447376 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780383700346 : ℝ)) (R := (0.780940182595 : ℝ)) (Q2 := (0.610559424204 : ℝ)) (T := (0.828271200278 : ℝ))
    (B := ((6872685763135033/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498117022747/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6867013716157783/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607798896101 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498117022747 : ℝ)) (s := (0.867109815220 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609759731408 : ℝ) ≤ 0.684687161926 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609759731408 : ℝ)) (Q := (0.609759731408 : ℝ))
      (s := (0.792586317037 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779872106520 : ℝ)) (R := (0.780428588769 : ℝ)) (Q2 := (0.609759731408 : ℝ)) (T := (0.827927198815 : ℝ))
    (B := ((6867013716157783/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (248460183127/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (857668496081127/1250000000000000) := by
  have hk1 : kappa q ≤ 0.607001219673 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496920366254 : ℝ)) (s := (0.867796145188 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608960580048 : ℝ) ≤ 0.684118729065 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608960580048 : ℝ)) (Q := (0.608960580048 : ℝ))
      (s := (0.793200486604 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779360523827 : ℝ)) (R := (0.779917006076 : ℝ)) (Q2 := (0.608960580048 : ℝ)) (T := (0.827583451501 : ℝ))
    (B := ((857668496081127/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495723709761/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (428480531913039/625000000000000) := by
  have hk1 : kappa q ≤ 0.606204083466 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495723709761 : ℝ)) (s := (0.868480283934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608161969534 : ℝ) ≤ 0.683550951585 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608161969534 : ℝ)) (Q := (0.608161969534 : ℝ))
      (s := (0.793812962110 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778848951911 : ℝ)) (R := (0.779405434160 : ℝ)) (Q2 := (0.608161969534 : ℝ)) (T := (0.827239957923 : ℝ))
    (B := ((428480531913039/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123631763317/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6850035332074217/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605407486891 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494527053268 : ℝ)) (s := (0.869162236632 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607363899276 : ℝ) ≤ 0.682983828280 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607363899276 : ℝ)) (Q := (0.607363899276 : ℝ))
      (s := (0.794423749555 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778337390415 : ℝ)) (R := (0.778893872664 : ℝ)) (Q2 := (0.607363899276 : ℝ)) (T := (0.826896717665 : ℝ))
    (B := ((6850035332074217/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19733215871/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844388423120899/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604611429363 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493330396775 : ℝ)) (s := (0.869842008424 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606566368688 : ℝ) ≤ 0.682417357949 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606566368688 : ℝ)) (Q := (0.606566368688 : ℝ))
      (s := (0.795032854904 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777825838983 : ℝ)) (R := (0.778382321232 : ℝ)) (Q2 := (0.606566368688 : ℝ)) (T := (0.826553730318 : ℝ))
    (B := ((6844388423120899/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246066870141/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838747773861047/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603815910301 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492133740282 : ℝ)) (s := (0.870519604418 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605769377187 : ℝ) ≤ 0.681851539395 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605769377187 : ℝ)) (Q := (0.605769377187 : ℝ))
      (s := (0.795640284088 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777314297262 : ℝ)) (R := (0.777870779511 : ℝ)) (Q2 := (0.605769377187 : ℝ)) (T := (0.826210995469 : ℝ))
    (B := ((6838747773861047/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (490937083789/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683311337444409/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603020929127 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490937083789 : ℝ)) (s := (0.871195029693 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604972924195 : ℝ) ≤ 0.681286371427 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604972924195 : ℝ)) (Q := (0.604972924195 : ℝ))
      (s := (0.796246042999 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776802764898 : ℝ)) (R := (0.777359247147 : ℝ)) (Q2 := (0.604972924195 : ℝ)) (T := (0.825868512713 : ℝ))
    (B := ((683311337444409/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15304388353/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827485215056293/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602226485264 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489740427296 : ℝ)) (s := (0.871868289292 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604177009133 : ℝ) ≤ 0.680721852854 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604177009133 : ℝ)) (Q := (0.604177009133 : ℝ))
      (s := (0.796850137501 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776291241539 : ℝ)) (R := (0.776847723788 : ℝ)) (Q2 := (0.604177009133 : ℝ)) (T := (0.825526281639 : ℝ))
    (B := ((6827485215056293/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488543770803/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852732910740067/1250000000000000) := by
  have hk1 : kappa q ≤ 0.601432578140 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488543770803 : ℝ)) (s := (0.872539388229 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603381631430 : ℝ) ≤ 0.680157982496 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603381631430 : ℝ)) (Q := (0.603381631430 : ℝ))
      (s := (0.797452573420 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775779726834 : ℝ)) (R := (0.776336209083 : ℝ)) (Q2 := (0.603381631430 : ℝ)) (T := (0.825184301847 : ℝ))
    (B := ((852732910740067/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487347114311/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1704061894324027/2500000000000000) := by
  have hk1 : kappa q ≤ 0.600639207187 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487347114311 : ℝ)) (s := (0.873208331484 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602586790514 : ℝ) ≤ 0.679594759171 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602586790514 : ℝ)) (Q := (0.602586790514 : ℝ))
      (s := (0.798053356549 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775268220433 : ℝ)) (R := (0.775824702682 : ℝ)) (Q2 := (0.602586790514 : ℝ)) (T := (0.824842572930 : ℝ))
    (B := ((1704061894324027/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243075228909/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702659519869621/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599846371837 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486150457818 : ℝ)) (s := (0.873875124010 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601792485818 : ℝ) ≤ 0.679032181703 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601792485818 : ℝ)) (Q := (0.601792485818 : ℝ))
      (s := (0.798652492649 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774756721987 : ℝ)) (R := (0.775313204236 : ℝ)) (Q2 := (0.601792485818 : ℝ)) (T := (0.824501094487 : ℝ))
    (B := ((1702659519869621/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19398152053/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402517391399561/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599054071529 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484953801325 : ℝ)) (s := (0.874539770726 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600998716779 : ℝ) ≤ 0.678470248923 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600998716779 : ℝ)) (Q := (0.600998716779 : ℝ))
      (s := (0.799249987445 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774245231148 : ℝ)) (R := (0.774801713397 : ℝ)) (Q2 := (0.600998716779 : ℝ)) (T := (0.824159866120 : ℝ))
    (B := ((3402517391399561/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1889676347/3906250000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27197750710501/40000000000000) := by
  have hk1 : kappa q ≤ 0.598262305702 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483757144832 : ℝ)) (s := (0.875202276519 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600205482837 : ℝ) ≤ 0.677908959665 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600205482837 : ℝ)) (Q := (0.600205482837 : ℝ))
      (s := (0.799845846631 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773733747570 : ℝ)) (R := (0.774290229819 : ℝ)) (Q2 := (0.600205482837 : ℝ)) (T := (0.823818887430 : ℝ))
    (B := ((27197750710501/40000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482560488339/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (339692337717983/500000000000000) := by
  have hk1 : kappa q ≤ 0.597471073799 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482560488339 : ℝ)) (s := (0.875862646249 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599412783430 : ℝ) ≤ 0.677348312763 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599412783430 : ℝ)) (Q := (0.599412783430 : ℝ))
      (s := (0.800440075872 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773222270906 : ℝ)) (R := (0.773778753155 : ℝ)) (Q2 := (0.599412783430 : ℝ)) (T := (0.823478158019 : ℝ))
    (B := ((339692337717983/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240681915923/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788262003440501/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596680375267 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481363831846 : ℝ)) (s := (0.876520884743 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598620618008 : ℝ) ≤ 0.676788307063 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598620618008 : ℝ)) (Q := (0.598620618008 : ℝ))
      (s := (0.801032680792 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772710800813 : ℝ)) (R := (0.773267283062 : ℝ)) (Q2 := (0.598620618008 : ℝ)) (T := (0.823137677494 : ℝ))
    (B := ((6788262003440501/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480167175353/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782682580034459/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595890209556 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480167175353 : ℝ)) (s := (0.877176996800 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597828986019 : ℝ) ≤ 0.676228941412 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597828986019 : ℝ)) (Q := (0.597828986019 : ℝ))
      (s := (0.801623666989 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772199336948 : ℝ)) (R := (0.772755819197 : ℝ)) (Q2 := (0.597828986019 : ℝ)) (T := (0.822797445464 : ℝ))
    (B := ((6782682580034459/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (23948525943/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777108931120423/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595100576117 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478970518860 : ℝ)) (s := (0.877830987186 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597037886910 : ℝ) ≤ 0.675670214655 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597037886910 : ℝ)) (Q := (0.597037886910 : ℝ))
      (s := (0.802213040030 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771687878966 : ℝ)) (R := (0.772244361215 : ℝ)) (Q2 := (0.597037886910 : ℝ)) (T := (0.822457461533 : ℝ))
    (B := ((6777108931120423/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12450 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477773862367/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771541428746709/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594311474406 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477773862367 : ℝ)) (s := (0.878482860641 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596247320141 : ℝ) ≤ 0.675112125653 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596247320141 : ℝ)) (Q := (0.596247320141 : ℝ))
      (s := (0.802800805446 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771176426528 : ℝ)) (R := (0.771732908777 : ℝ)) (Q2 := (0.596247320141 : ℝ)) (T := (0.822117725317 : ℝ))
    (B := ((6771541428746709/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S4
namespace BstLean.Part269.S4
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12450 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.053014386999 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S4.wn_upper (by omega : 12450 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010703013126 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036170142337)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010703013126 + 2 * 0.737676 / 12450) := by gcongr
    _ ≤ (0.053014386999 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12450 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12450 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.579568022106 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12450 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.579568022106 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12450 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003795409572 + 0.003362150420 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003795409572 + 0.003362150420 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.579568022106 ≤ R)
    (hB : (X + 0.053014386999 + R + 0.008566524203) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008566524203 := by
    convert (BstLean.Part269.S4.finite_centre_upper (by omega : 12450 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (86179296547/1000000000000)
  | 2 => (87135410839/1000000000000)
  | 3 => (5505732873/62500000000)
  | 4 => (89050126217/1000000000000)
  | 5 => (45006436921/500000000000)
  | 6 => (90982662963/1000000000000)
  | 7 => (9196267813/100000000000)
  | 8 => (1161958219/12500000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003795409572 + 0.003362150420 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219789620578 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011076109189 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003795409572 + 0.003362150420 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.221356425384 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011192225026 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003795409572 + 0.003362150420 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222902843864 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011307957342 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003795409572 + 0.003362150420 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224429080731 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011423314545 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003795409572 + 0.003362150420 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225935335654 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011538304801 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003795409572 + 0.003362150420 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227421801765 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011652935923 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003795409572 + 0.003362150420 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228888667520 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011767215514 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12450 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003795409572 + 0.003362150420 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.230336115232 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011881150848 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12450 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g) :
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

end BstLean.Part269.S4

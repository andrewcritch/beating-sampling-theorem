import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S6
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12500 ≤ n) : wn n ≤ 1.036097087640 := by
  have hnR : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.803398874989 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.803398874989 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036097087640 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12500 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12500 + 24 / (12500 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12500 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008549299638 : ℝ) := by
  have hnR : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.803398874989 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12500 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036097087640 * (81 / 1000 / 12500)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036097087640 * n *
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
        4 * (1 / 2.506628) * 1.036097087640 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036097087640 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036097087640 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12500)) / 111.803398874989 := by gcongr
    _ ≤ (0.008549299638 : ℝ) := by norm_num

end BstLean.Part269.S6
namespace BstLean.Part269.S6
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12500 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12500 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12500 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12500 + 0.008549299638 / 111.803398874989) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12500 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12500 := by gcongr
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
  have hn : (111.803398874989 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S6.finite_centre_upper (by omega : 12500 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528038918631/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3505313960204937/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627921882254 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528038918631 : ℝ)) (s := (0.849220171929 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629914659276 : ℝ) ≤ 0.699113573762 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629914659276 : ℝ)) (Q := (0.629914659276 : ℝ))
      (s := (0.776664356096 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792667573611 : ℝ)) (R := (0.793221829931 : ℝ)) (Q2 := (0.629914659276 : ℝ)) (T := (0.836603977250 : ℝ))
    (B := ((3505313960204937/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263421405247/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (70048043341391/100000000000000) := by
  have hk1 : kappa q ≤ 0.627110869134 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526842810494 : ℝ)) (s := (0.849962736261 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629102158203 : ℝ) ≤ 0.698528620509 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629102158203 : ℝ)) (Q := (0.629102158203 : ℝ))
      (s := (0.777322632209 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792155836395 : ℝ)) (R := (0.792710092715 : ℝ)) (Q2 := (0.629102158203 : ℝ)) (T := (0.836253907787 : ℝ))
    (B := ((70048043341391/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525646702357/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (139979745863733/200000000000000) := by
  have hk1 : kappa q ≤ 0.626300411449 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525646702357 : ℝ)) (s := (0.850702970667 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628290213218 : ℝ) ≤ 0.697944353519 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628290213218 : ℝ)) (Q := (0.628290213218 : ℝ))
      (s := (0.777979053687 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791644119191 : ℝ)) (R := (0.792198375511 : ℝ)) (Q2 := (0.628290213218 : ℝ)) (T := (0.835904102675 : ℝ))
    (B := ((139979745863733/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (26222529711/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1748294196647501/2500000000000000) := by
  have hk1 : kappa q ≤ 0.625490508536 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524450594220 : ℝ)) (s := (0.851440881226 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478823656 : ℝ) ≤ 0.697360771485 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478823656 : ℝ)) (Q := (0.627478823656 : ℝ))
      (s := (0.778633627494 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791132421619 : ℝ)) (R := (0.791686677939 : ℝ)) (Q2 := (0.627478823656 : ℝ)) (T := (0.835554561463 : ℝ))
    (B := ((1748294196647501/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523254486083/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987372803430269/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624681159731 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523254486083 : ℝ)) (s := (0.852176473974 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667988851 : ℝ) ≤ 0.696777873101 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667988851 : ℝ)) (Q := (0.626667988851 : ℝ))
      (s := (0.779286360557 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790620743297 : ℝ)) (R := (0.791174999617 : ℝ)) (Q2 := (0.626667988851 : ℝ)) (T := (0.835205283699 : ℝ))
    (B := ((6987372803430269/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261029188973/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (218174229150997/312500000000000) := by
  have hk1 : kappa q ≤ 0.623872364377 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522058377946 : ℝ)) (s := (0.852909754908 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625857708147 : ℝ) ≤ 0.696195657072 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625857708147 : ℝ)) (Q := (0.625857708147 : ℝ))
      (s := (0.779937259755 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790109083847 : ℝ)) (R := (0.790663340167 : ℝ)) (Q2 := (0.625857708147 : ℝ)) (T := (0.834856268938 : ℝ))
    (B := ((218174229150997/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520862269809/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975784363962449/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623064121816 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520862269809 : ℝ)) (s := (0.853640729986 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625047980883 : ℝ) ≤ 0.695614122096 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625047980883 : ℝ)) (Q := (0.625047980883 : ℝ))
      (s := (0.780586331929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789597442889 : ℝ)) (R := (0.790151699209 : ℝ)) (Q2 := (0.625047980883 : ℝ)) (T := (0.834507516728 : ℝ))
    (B := ((6975784363962449/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64958270209/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1393999977206451/2000000000000000) := by
  have hk1 : kappa q ≤ 0.622256431395 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519666161672 : ℝ)) (s := (0.854369405125 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624238806406 : ℝ) ≤ 0.695033266884 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624238806406 : ℝ)) (Q := (0.624238806406 : ℝ))
      (s := (0.781233583877 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789085820045 : ℝ)) (R := (0.789640076365 : ℝ)) (Q2 := (0.624238806406 : ℝ)) (T := (0.834159026626 : ℝ))
    (B := ((1393999977206451/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16202189173/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964221888294213/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621449292465 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518470053536 : ℝ)) (s := (0.855095786206 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623430184064 : ℝ) ≤ 0.694453090147 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623430184064 : ℝ)) (Q := (0.623430184064 : ℝ))
      (s := (0.781879022355 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788574214938 : ℝ)) (R := (0.789128471258 : ℝ)) (Q2 := (0.623430184064 : ℝ)) (T := (0.833810798186 : ℝ))
    (B := ((6964221888294213/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517273945399/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958450360043493/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620642704378 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517273945399 : ℝ)) (s := (0.855819879070 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622622113210 : ℝ) ≤ 0.693873590601 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622622113210 : ℝ)) (Q := (0.622622113210 : ℝ))
      (s := (0.782522654076 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788062627193 : ℝ)) (R := (0.788616883513 : ℝ)) (Q2 := (0.622622113210 : ℝ)) (T := (0.833462830966 : ℝ))
    (B := ((6958450360043493/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258038918631/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3476342645308639/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619836666491 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516077837262 : ℝ)) (s := (0.856541689521 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621814593199 : ℝ) ≤ 0.693294766967 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621814593199 : ℝ)) (Q := (0.621814593199 : ℝ))
      (s := (0.783164485715 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787551056435 : ℝ)) (R := (0.788105312755 : ℝ)) (Q2 := (0.621814593199 : ℝ)) (T := (0.833115124523 : ℝ))
    (B := ((3476342645308639/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4119053833/8000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389385333878901/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619031178164 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514881729125 : ℝ)) (s := (0.857261223324 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621007623390 : ℝ) ≤ 0.692716617969 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621007623390 : ℝ)) (Q := (0.621007623390 : ℝ))
      (s := (0.783804523904 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787039502290 : ℝ)) (R := (0.787593758610 : ℝ)) (Q2 := (0.621007623390 : ℝ)) (T := (0.832767678418 : ℝ))
    (B := ((1389385333878901/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128421405247/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3470587242897803/5000000000000000) := by
  have hk1 : kappa q ≤ 0.618226238757 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513685620988 : ℝ)) (s := (0.857978486205 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620201203142 : ℝ) ≤ 0.692139142334 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620201203142 : ℝ)) (Q := (0.620201203142 : ℝ))
      (s := (0.784442775237 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786527964384 : ℝ)) (R := (0.787082220704 : ℝ)) (Q2 := (0.620201203142 : ℝ)) (T := (0.832420492210 : ℝ))
    (B := ((3470587242897803/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512489512851/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27741714917129/40000000000000) := by
  have hk1 : kappa q ≤ 0.617421847638 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512489512851 : ℝ)) (s := (0.858693483857 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619395331821 : ℝ) ≤ 0.691562338796 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619395331821 : ℝ)) (Q := (0.619395331821 : ℝ))
      (s := (0.785079246267 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786016442346 : ℝ)) (R := (0.786570698666 : ℝ)) (Q2 := (0.619395331821 : ℝ)) (T := (0.832073565465 : ℝ))
    (B := ((27741714917129/40000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255646702357/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929689389357093/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616618004175 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511293404714 : ℝ)) (s := (0.859406221933 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618590008795 : ℝ) ≤ 0.690986206093 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618590008795 : ℝ)) (Q := (0.618590008795 : ℝ))
      (s := (0.785713943506 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785504935806 : ℝ)) (R := (0.786059192126 : ℝ)) (Q2 := (0.618590008795 : ℝ)) (T := (0.831726897746 : ℝ))
    (B := ((6929689389357093/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510097296577/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923956455563523/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615814707739 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510097296577 : ℝ)) (s := (0.860116706050 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617785233433 : ℝ) ≤ 0.690410742962 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617785233433 : ℝ)) (Q := (0.617785233433 : ℝ))
      (s := (0.786346873430 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784993444393 : ℝ)) (R := (0.785547700713 : ℝ)) (Q2 := (0.617785233433 : ℝ)) (T := (0.831380488618 : ℝ))
    (B := ((6923956455563523/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12722529711/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918229917485411/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615011957706 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508901188440 : ℝ)) (s := (0.860824941789 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616981005110 : ℝ) ≤ 0.689835948151 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616981005110 : ℝ)) (Q := (0.616981005110 : ℝ))
      (s := (0.786978042473 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784481967738 : ℝ)) (R := (0.785036224058 : ℝ)) (Q2 := (0.616981005110 : ℝ)) (T := (0.831034337650 : ℝ))
    (B := ((6918229917485411/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507705080303/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1382501952949373/2000000000000000) := by
  have hk1 : kappa q ≤ 0.614209753454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507705080303 : ℝ)) (s := (0.861530934694 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616177323204 : ℝ) ≤ 0.689261820410 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616177323204 : ℝ)) (Q := (0.616177323204 : ℝ))
      (s := (0.787607457030 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783970505475 : ℝ)) (R := (0.784524761795 : ℝ)) (Q2 := (0.616177323204 : ℝ)) (T := (0.830688444411 : ℝ))
    (B := ((1382501952949373/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253254486083/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906795987011983/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613408094364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506508972166 : ℝ)) (s := (0.862234690276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615374187094 : ℝ) ≤ 0.688688358491 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615374187094 : ℝ)) (Q := (0.615374187094 : ℝ))
      (s := (0.788235123462 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783459057236 : ℝ)) (R := (0.784013313556 : ℝ)) (Q2 := (0.615374187094 : ℝ)) (T := (0.830342808471 : ℝ))
    (B := ((6906795987011983/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505312864029/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6901088573984613/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612606979821 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505312864029 : ℝ)) (s := (0.862936214009 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614571596162 : ℝ) ≤ 0.688115561151 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614571596162 : ℝ)) (Q := (0.614571596162 : ℝ))
      (s := (0.788861048089 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782947622655 : ℝ)) (R := (0.783501878975 : ℝ)) (Q2 := (0.614571596162 : ℝ)) (T := (0.829997429401 : ℝ))
    (B := ((6901088573984613/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126029188973/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895387515408107/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611806409212 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504116755892 : ℝ)) (s := (0.863635511330 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613769549798 : ℝ) ≤ 0.687543427154 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613769549798 : ℝ)) (Q := (0.613769549798 : ℝ))
      (s := (0.789485237190 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782436201369 : ℝ)) (R := (0.782990457689 : ℝ)) (Q2 := (0.613769549798 : ℝ)) (T := (0.829652306778 : ℝ))
    (B := ((6895387515408107/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100584129551/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889692801065087/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611006381928 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502920647755 : ℝ)) (s := (0.864332587644 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612968047388 : ℝ) ≤ 0.686971955265 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612968047388 : ℝ)) (Q := (0.612968047388 : ℝ))
      (s := (0.790107697015 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781924793013 : ℝ)) (R := (0.782479049333 : ℝ)) (Q2 := (0.612968047388 : ℝ)) (T := (0.829307440175 : ℝ))
    (B := ((6889692801065087/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250862269809/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884004420777203/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610206897362 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501724539618 : ℝ)) (s := (0.865027448319 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612167088327 : ℝ) ≤ 0.686401144255 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612167088327 : ℝ)) (Q := (0.612167088327 : ℝ))
      (s := (0.790728433769 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781413397225 : ℝ)) (R := (0.781967653545 : ℝ)) (Q2 := (0.612167088327 : ℝ)) (T := (0.828962829170 : ℝ))
    (B := ((6884004420777203/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500528431481/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1375664472880981/2000000000000000) := by
  have hk1 : kappa q ≤ 0.609407954912 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500528431481 : ℝ)) (s := (0.865720098692 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611366672011 : ℝ) ≤ 0.685830992900 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611366672011 : ℝ)) (Q := (0.611366672011 : ℝ))
      (s := (0.791347453623 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780902013644 : ℝ)) (R := (0.781456269964 : ℝ)) (Q2 := (0.611366672011 : ℝ)) (T := (0.828618473342 : ℝ))
    (B := ((1375664472880981/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31208270209/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1718161655461801/2500000000000000) := by
  have hk1 : kappa q ≤ 0.608609553978 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499332323344 : ℝ)) (s := (0.866410544064 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610566797837 : ℝ) ≤ 0.685261499976 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610566797837 : ℝ)) (Q := (0.610566797837 : ℝ))
      (s := (0.791964762714 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780390641909 : ℝ)) (R := (0.780944898229 : ℝ)) (Q2 := (0.610566797837 : ℝ)) (T := (0.828274372271 : ℝ))
    (B := ((1718161655461801/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62267026901/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433488591520721/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607811693963 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498136215208 : ℝ)) (s := (0.867098789700 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609767465209 : ℝ) ≤ 0.684692664269 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609767465209 : ℝ)) (Q := (0.609767465209 : ℝ))
      (s := (0.792580367138 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779879281661 : ℝ)) (R := (0.780433537981 : ℝ)) (Q2 := (0.609767465209 : ℝ)) (T := (0.827930525539 : ℝ))
    (B := ((3433488591520721/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496940107071/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430657018981533/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607014374274 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496940107071 : ℝ)) (s := (0.867784840836 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608968673532 : ℝ) ≤ 0.684124484566 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608968673532 : ℝ)) (Q := (0.608968673532 : ℝ))
      (s := (0.793194272961 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779367932542 : ℝ)) (R := (0.779922188862 : ℝ)) (Q2 := (0.608968673532 : ℝ)) (T := (0.827586932730 : ℝ))
    (B := ((3430657018981533/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247871999467/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855657176625399/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606217594320 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495743998934 : ℝ)) (s := (0.868468702673 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608170422215 : ℝ) ≤ 0.683556959659 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608170422215 : ℝ)) (Q := (0.608170422215 : ℝ))
      (s := (0.793806486207 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778856594195 : ℝ)) (R := (0.779410850515 : ℝ)) (Q2 := (0.608170422215 : ℝ)) (T := (0.827243593429 : ℝ))
    (B := ((6855657176625399/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494547890797/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1370001317815883/2000000000000000) := by
  have hk1 : kappa q ≤ 0.605421353513 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494547890797 : ℝ)) (s := (0.869150380377 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607372710668 : ℝ) ≤ 0.682990088343 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607372710668 : ℝ)) (Q := (0.607372710668 : ℝ))
      (s := (0.794417012870 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778345266263 : ℝ)) (R := (0.778899522583 : ℝ)) (Q2 := (0.607372710668 : ℝ)) (T := (0.826900507223 : ℝ))
    (B := ((1370001317815883/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24667589133/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1711090566353379/2500000000000000) := by
  have hk1 : kappa q ≤ 0.604625651270 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493351782660 : ℝ)) (s := (0.869829879084 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606575538307 : ℝ) ≤ 0.682423869419 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606575538307 : ℝ)) (Q := (0.606575538307 : ℝ))
      (s := (0.795025858905 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777833948392 : ℝ)) (R := (0.778388204712 : ℝ)) (Q2 := (0.606575538307 : ℝ)) (T := (0.826557673701 : ℝ))
    (B := ((1711090566353379/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492155674523/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683872419575331/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603830487010 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492155674523 : ℝ)) (s := (0.870507203896 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605778904549 : ℝ) ≤ 0.681858301693 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605778904549 : ℝ)) (Q := (0.605778904549 : ℝ))
      (s := (0.795633030237 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777322640228 : ℝ)) (R := (0.777876896548 : ℝ)) (Q2 := (0.605778904549 : ℝ)) (T := (0.826215092454 : ℝ))
    (B := ((683872419575331/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245479783193/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416546185130697/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603035860155 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490959566386 : ℝ)) (s := (0.871182359885 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604982808817 : ℝ) ≤ 0.681293383973 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604982808817 : ℝ)) (Q := (0.604982808817 : ℝ))
      (s := (0.796238532751 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776811341418 : ℝ)) (R := (0.777365597738 : ℝ)) (Q2 := (0.604982808817 : ℝ)) (T := (0.825872763074 : ℝ))
    (B := ((3416546185130697/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489763458249/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827466779137133/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602241770130 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489763458249 : ℝ)) (s := (0.871855352088 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604187250534 : ℝ) ≤ 0.680729115073 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604187250534 : ℝ)) (Q := (0.604187250534 : ℝ))
      (s := (0.796842372300 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776300051611 : ℝ)) (R := (0.776854307931 : ℝ)) (Q2 := (0.604187250534 : ℝ)) (T := (0.825530685153 : ℝ))
    (B := ((6827466779137133/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15267729691/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3410923706308223/5000000000000000) := by
  have hk1 : kappa q ≤ 0.601448216364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488567350112 : ℝ)) (s := (0.872526185513 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603392229127 : ℝ) ≤ 0.680165493811 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603392229127 : ℝ)) (Q := (0.603392229127 : ℝ))
      (s := (0.797444554706 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775788770455 : ℝ)) (R := (0.776343026775 : ℝ)) (Q2 := (0.603392229127 : ℝ)) (T := (0.825188858290 : ℝ))
    (B := ((3410923706308223/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19494849679/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816234260971591/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600655198288 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487371241975 : ℝ)) (s := (0.873194865134 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602597744028 : ℝ) ≤ 0.679602519008 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602597744028 : ℝ)) (Q := (0.602597744028 : ℝ))
      (s := (0.798045085752 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775277497602 : ℝ)) (R := (0.775831753922 : ℝ)) (Q2 := (0.602597744028 : ℝ)) (T := (0.824847282079 : ℝ))
    (B := ((6816234260971591/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243087566919/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702656828627739/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599862715336 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486175133838 : ℝ)) (s := (0.873861395897 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601803794669 : ℝ) ≤ 0.679040189492 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601803794669 : ℝ)) (Q := (0.601803794669 : ℝ))
      (s := (0.798643971193 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774766232703 : ℝ)) (R := (0.775320489023 : ℝ)) (Q2 := (0.601803794669 : ℝ)) (T := (0.824505956121 : ℝ))
    (B := ((1702656828627739/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484979025701/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6805026563578843/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599070766947 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484979025701 : ℝ)) (s := (0.874525782714 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601010380487 : ℝ) ≤ 0.678478504091 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601010380487 : ℝ)) (Q := (0.601010380487 : ℝ))
      (s := (0.799241216747 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774254975410 : ℝ)) (R := (0.774809231730 : ℝ)) (Q2 := (0.601010380487 : ℝ)) (T := (0.824164880015 : ℝ))
    (B := ((6805026563578843/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120945729391/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1359886399711053/2000000000000000) := by
  have hk1 : kappa q ≤ 0.598279352561 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483782917564 : ℝ)) (s := (0.875188030468 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600217500923 : ℝ) ≤ 0.677917461643 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600217500923 : ℝ)) (Q := (0.600217500923 : ℝ))
      (s := (0.799836828101 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773743725378 : ℝ)) (R := (0.774297981698 : ℝ)) (Q2 := (0.600217500923 : ℝ)) (T := (0.823824053365 : ℝ))
    (B := ((1359886399711053/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482586809427/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793843609855733/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597488471621 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482586809427 : ℝ)) (s := (0.875848144011 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599425155418 : ℝ) ≤ 0.677357060984 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599425155418 : ℝ)) (Q := (0.599425155418 : ℝ))
      (s := (0.800430810909 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773232482260 : ℝ)) (R := (0.773786738580 : ℝ)) (Q2 := (0.599425155418 : ℝ)) (T := (0.823483475774 : ℝ))
    (B := ((6793843609855733/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48139070129/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788261387931059/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596698123577 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481390701290 : ℝ)) (s := (0.876506128166 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598633343420 : ℝ) ≤ 0.676797300961 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598633343420 : ℝ)) (Q := (0.598633343420 : ℝ))
      (s := (0.801023170793 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772721245714 : ℝ)) (R := (0.773275502034 : ℝ)) (Q2 := (0.598633343420 : ℝ)) (T := (0.823143146850 : ℝ))
    (B := ((6788261387931059/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480194593153/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3391342189676387/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595908307877 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480194593153 : ℝ)) (s := (0.877161987724 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597842064377 : ℝ) ≤ 0.676238180420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597842064377 : ℝ)) (Q := (0.597842064377 : ℝ))
      (s := (0.801613913341 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772210015396 : ℝ)) (R := (0.772764271716 : ℝ)) (Q2 := (0.597842064377 : ℝ)) (T := (0.822803066198 : ℝ))
    (B := ((3391342189676387/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (59874810627/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1694278313957257/2500000000000000) := by
  have hk1 : kappa q ≤ 0.595119023974 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478998485016 : ℝ)) (s := (0.877815727447 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597051317741 : ℝ) ≤ 0.675679698213 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597051317741 : ℝ)) (Q := (0.597051317741 : ℝ))
      (s := (0.802203044113 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771698790964 : ℝ)) (R := (0.772253047284 : ℝ)) (Q2 := (0.597051317741 : ℝ)) (T := (0.822463233429 : ℝ))
    (B := ((1694278313957257/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12500 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477802376879/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (846443534161757/1250000000000000) := by
  have hk1 : kappa q ≤ 0.594330271325 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477802376879 : ℝ)) (s := (0.878467352068 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596261102967 : ℝ) ≤ 0.675121853196 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596261102967 : ℝ)) (Q := (0.596261102967 : ℝ))
      (s := (0.802790568635 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771187572077 : ℝ)) (R := (0.771741828397 : ℝ)) (Q2 := (0.596261102967 : ℝ)) (T := (0.822123648152 : ℝ))
    (B := ((846443534161757/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S6
namespace BstLean.Part269.S6
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12500 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052907092068 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S6.wn_upper (by omega : 12500 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010681585651 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036097087640)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010681585651 + 2 * 0.737676 / 12500) := by gcongr
    _ ≤ (0.052907092068 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12500 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12500 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.803398874989 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12500 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.803398874989 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12500 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003740909217 + 0.003348232271 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003740909217 + 0.003348232271 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.803398874989 ≤ R)
    (hB : (X + 0.052907092068 + R + 0.008549299638) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008549299638 := by
    convert (BstLean.Part269.S6.finite_centre_upper (by omega : 12500 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (86021369179/1000000000000)
  | 2 => (43487146527/500000000000)
  | 3 => (87926907033/1000000000000)
  | 4 => (88880981337/1000000000000)
  | 5 => (22459661161/250000000000)
  | 6 => (45401217841/500000000000)
  | 7 => (11471919921/125000000000)
  | 8 => (92760947499/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003740909217 + 0.003348232271 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219650573144 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011053934774 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003740909217 + 0.003348232271 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.221218136381 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011169818147 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003740909217 + 0.003348232271 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222765290034 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011285318766 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003740909217 + 0.003348232271 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224292239623 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011400445023 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003740909217 + 0.003348232271 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225799185585 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011515205068 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003740909217 + 0.003348232271 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227286321780 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011629606699 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003740909217 + 0.003348232271 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228753837356 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011743657501 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12500 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003740909217 + 0.003348232271 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.230201915289 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011857364736 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12500 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g) :
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

end BstLean.Part269.S6

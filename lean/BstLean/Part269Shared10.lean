import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S10
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12600 ≤ n) : wn n ≤ 1.035952292573 := by
  have hnR : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.249721603218 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.249721603218 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035952292573 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12600 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12600 + 24 / (12600 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12600 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008515159490 : ℝ) := by
  have hnR : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.249721603218 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12600 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035952292573 * (81 / 1000 / 12600)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035952292573 * n *
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
        4 * (1 / 2.506628) * 1.035952292573 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035952292573 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035952292573 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12600)) / 112.249721603218 := by gcongr
    _ ≤ (0.008515159490 : ℝ) := by norm_num

end BstLean.Part269.S10
namespace BstLean.Part269.S10
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12600 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12600 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12600 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12600 + 0.008515159490 / 112.249721603218) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12600 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12600 := by gcongr
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
  have hn : (112.249721603218 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S10.finite_centre_upper (by omega : 12600 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (10560995717/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010423541265619/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627929253248 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528049785850 : ℝ)) (s := (0.849213414675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629911876902 : ℝ) ≤ 0.699111570127 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629911876902 : ℝ)) (Q := (0.629911876902 : ℝ))
      (s := (0.776666612736 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792670220612 : ℝ)) (R := (0.793220078073 : ℝ)) (Q2 := (0.629911876902 : ℝ)) (T := (0.836602778410 : ℝ))
    (B := ((7010423541265619/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105370952887/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (350230270219539/500000000000000) := by
  have hk1 : kappa q ≤ 0.627118971674 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526854764435 : ℝ)) (s := (0.849955326587 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629100113223 : ℝ) ≤ 0.698527148604 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629100113223 : ℝ)) (Q := (0.629100113223 : ℝ))
      (s := (0.777324287247 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792158946848 : ℝ)) (R := (0.792708804309 : ℝ)) (Q2 := (0.629100113223 : ℝ)) (T := (0.836253026730 : ℝ))
    (B := ((350230270219539/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (26282987151/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998793800784669/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626309244535 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525659743020 : ℝ)) (s := (0.850694912744 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628288904629 : ℝ) ≤ 0.697943412102 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628288904629 : ℝ)) (Q := (0.628288904629 : ℝ))
      (s := (0.777980110492 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791647693063 : ℝ)) (R := (0.792197550524 : ℝ)) (Q2 := (0.628288904629 : ℝ)) (T := (0.835903538923 : ℝ))
    (B := ((6998793800784669/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131116180401/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1748247179878711/2500000000000000) := by
  have hk1 : kappa q ≤ 0.625500071166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524464721604 : ℝ)) (s := (0.851432179210 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478250455 : ℝ) ≤ 0.697360359318 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478250455 : ℝ)) (Q := (0.627478250455 : ℝ))
      (s := (0.778634089420 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791136458876 : ℝ)) (R := (0.791686316337 : ℝ)) (Q2 := (0.627478250455 : ℝ)) (T := (0.835554314540 : ℝ))
    (B := ((1748247179878711/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523269700189/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987190149692329/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624691450908 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523269700189 : ℝ)) (s := (0.852167132002 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668150043 : ℝ) ≤ 0.696777988952 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668150043 : ℝ)) (Q := (0.626668150043 : ℝ))
      (s := (0.779286230933 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790625243909 : ℝ)) (R := (0.791175101370 : ℝ)) (Q2 := (0.626668150043 : ℝ)) (T := (0.835205353132 : ℝ))
    (B := ((6987190149692329/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261037339387/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981398080471347/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623883383103 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522074678774 : ℝ)) (s := (0.852899777104 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625858602729 : ℝ) ≤ 0.696196299705 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625858602729 : ℝ)) (Q := (0.625858602729 : ℝ))
      (s := (0.779936541900 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790114047781 : ℝ)) (R := (0.790663905242 : ℝ)) (Q2 := (0.625858602729 : ℝ)) (T := (0.834856654251 : ℝ))
    (B := ((6981398080471347/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520879657359/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (87195156263113/125000000000000) := by
  have hk1 : kappa q ≤ 0.623075867096 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520879657359 : ℝ)) (s := (0.853630120456 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625049607859 : ℝ) ≤ 0.695615290284 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625049607859 : ℝ)) (Q := (0.625049607859 : ℝ))
      (s := (0.780585029139 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789602870115 : ℝ)) (R := (0.790152727576 : ℝ)) (Q2 := (0.625049607859 : ℝ)) (T := (0.834508217448 : ℝ))
    (B := ((87195156263113/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64960579493/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (871229175083151/1250000000000000) := by
  have hk1 : kappa q ≤ 0.622268902236 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519684635944 : ℝ)) (s := (0.854358167963 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624241164782 : ℝ) ≤ 0.695034959403 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624241164782 : ℝ)) (Q := (0.624241164782 : ℝ))
      (s := (0.781231699429 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789091710534 : ℝ)) (R := (0.789641567995 : ℝ)) (Q2 := (0.624241164782 : ℝ)) (T := (0.834160042282 : ℝ))
    (B := ((871229175083151/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518489614529/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3482030384301019/5000000000000000) := by
  have hk1 : kappa q ≤ 0.621462487875 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518489614529 : ℝ)) (s := (0.855083925487 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623433272848 : ℝ) ≤ 0.694455305775 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623433272848 : ℝ)) (Q := (0.623433272848 : ℝ))
      (s := (0.781876559507 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788580568663 : ℝ)) (R := (0.789130426124 : ℝ)) (Q2 := (0.623433272848 : ℝ)) (T := (0.833812128307 : ℝ))
    (B := ((3482030384301019/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258647296557/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958294594183841/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620656623368 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517294593114 : ℝ)) (s := (0.855807398856 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622625931410 : ℝ) ≤ 0.693876328122 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622625931410 : ℝ)) (Q := (0.622625931410 : ℝ))
      (s := (0.782519616071 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788069444126 : ℝ)) (R := (0.788619301587 : ℝ)) (Q2 := (0.622625931410 : ℝ)) (T := (0.833464475083 : ℝ))
    (B := ((6958294594183841/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516099571699/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (869066858347099/1250000000000000) := by
  have hk1 : kappa q ≤ 0.619851308072 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516099571699 : ℝ)) (s := (0.856528593856 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621819139826 : ℝ) ≤ 0.693298025165 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621819139826 : ℝ)) (Q := (0.621819139826 : ℝ))
      (s := (0.783160875776 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787558336550 : ℝ)) (R := (0.788108194011 : ℝ)) (Q2 := (0.621819139826 : ℝ)) (T := (0.833117082168 : ℝ))
    (B := ((869066858347099/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128726137571/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6946781575788667/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619046541349 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514904550284 : ℝ)) (s := (0.857247516239 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621012897455 : ℝ) ≤ 0.692720395634 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621012897455 : ℝ)) (Q := (0.621012897455 : ℝ))
      (s := (0.783800345238 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787047245562 : ℝ)) (R := (0.787597103023 : ℝ)) (Q2 := (0.621012897455 : ℝ)) (T := (0.832769949125 : ℝ))
    (B := ((6946781575788667/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513709528869/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1735258677667147/2500000000000000) := by
  have hk1 : kappa q ≤ 0.618242322562 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513709528869 : ℝ)) (s := (0.857964171717 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620207203660 : ℝ) ≤ 0.692143438259 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620207203660 : ℝ)) (Q := (0.620207203660 : ℝ))
      (s := (0.784438031032 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786536170789 : ℝ)) (R := (0.787086028250 : ℝ)) (Q2 := (0.620207203660 : ℝ)) (T := (0.832423075513 : ℝ))
    (B := ((1735258677667147/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256257253727/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935294260906767/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617438651079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512514507454 : ℝ)) (s := (0.858678565966 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619402057806 : ℝ) ≤ 0.691567151776 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619402057806 : ℝ)) (Q := (0.619402057806 : ℝ))
      (s := (0.785073939694 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786025111861 : ℝ)) (R := (0.786574969322 : ℝ)) (Q2 := (0.619402057806 : ℝ)) (T := (0.832076460899 : ℝ))
    (B := ((6935294260906767/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511319486039/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1385912043206851/2000000000000000) := by
  have hk1 : kappa q ≤ 0.616635526271 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511319486039 : ℝ)) (s := (0.859390704626 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618597459266 : ℝ) ≤ 0.690991534927 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618597459266 : ℝ)) (Q := (0.618597459266 : ℝ))
      (s := (0.785708077717 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785514068409 : ℝ)) (R := (0.786063925870 : ℝ)) (Q2 := (0.618597459266 : ℝ)) (T := (0.831730104848 : ℝ))
    (B := ((1385912043206851/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510124464623/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (216369767675709/312500000000000) := by
  have hk1 : kappa q ≤ 0.615832947509 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510124464623 : ℝ)) (s := (0.860100593299 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617793407407 : ℝ) ≤ 0.690416586454 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617793407407 : ℝ)) (Q := (0.617793407407 : ℝ))
      (s := (0.786340451564 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785003040062 : ℝ)) (R := (0.785552897523 : ℝ)) (Q2 := (0.617793407407 : ℝ)) (T := (0.831384006926 : ℝ))
    (B := ((216369767675709/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63616180401/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1729527824821011/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615030914173 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508929443208 : ℝ)) (s := (0.860808237552 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616989901608 : ℝ) ≤ 0.689842305106 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616989901608 : ℝ)) (Q := (0.616989901608 : ℝ))
      (s := (0.786971067648 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784492026454 : ℝ)) (R := (0.785041883915 : ℝ)) (Q2 := (0.616989901608 : ℝ)) (T := (0.831038166702 : ℝ))
    (B := ((1729527824821011/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507734421793/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (691239640667039/1000000000000000) := by
  have hk1 : kappa q ≤ 0.614229425641 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507734421793 : ℝ)) (s := (0.861513642914 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616186941250 : ℝ) ≤ 0.689268689638 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616186941250 : ℝ)) (Q := (0.616186941250 : ℝ))
      (s := (0.787599932347 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783981027219 : ℝ)) (R := (0.784530884680 : ℝ)) (Q2 := (0.616186941250 : ℝ)) (T := (0.830692583748 : ℝ))
    (B := ((691239640667039/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253269700189/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3453343938736821/5000000000000000) := by
  have hk1 : kappa q ≤ 0.613428481296 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506539400378 : ℝ)) (s := (0.862216814882 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615384525709 : ℝ) ≤ 0.688695738803 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615384525709 : ℝ)) (Q := (0.615384525709 : ℝ))
      (s := (0.788227052009 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783470041989 : ℝ)) (R := (0.784019899450 : ℝ)) (Q2 := (0.615384525709 : ℝ)) (T := (0.830347257633 : ℝ))
    (B := ((3453343938736821/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505344378963/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1725246425356331/2500000000000000) := by
  have hk1 : kappa q ≤ 0.612628080525 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505344378963 : ℝ)) (s := (0.862917758915 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614582654375 : ℝ) ≤ 0.688123451366 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614582654375 : ℝ)) (Q := (0.614582654375 : ℝ))
      (s := (0.788852432932 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782959070401 : ℝ)) (R := (0.783508927862 : ℝ)) (Q2 := (0.614582654375 : ℝ)) (T := (0.830002187933 : ℝ))
    (B := ((1725246425356331/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126037339387/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (275811594731853/400000000000000) := by
  have hk1 : kappa q ≤ 0.611828222715 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504149357548 : ℝ)) (s := (0.863616480438 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613781326632 : ℝ) ≤ 0.687551826089 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613781326632 : ℝ)) (Q := (0.613781326632 : ℝ))
      (s := (0.789476081385 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782448112090 : ℝ)) (R := (0.782997969551 : ℝ)) (Q2 := (0.613781326632 : ℝ)) (T := (0.829657374221 : ℝ))
    (B := ((275811594731853/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502954336133/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444800183948331/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611028907260 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502954336133 : ℝ)) (s := (0.864312984842 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612980541872 : ℝ) ≤ 0.686980861741 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612980541872 : ℝ)) (Q := (0.612980541872 : ℝ))
      (s := (0.790098003596 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781937166694 : ℝ)) (R := (0.782487024155 : ℝ)) (Q2 := (0.612980541872 : ℝ)) (T := (0.829312816073 : ℝ))
    (B := ((3444800183948331/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250879657359/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1376783438015049/2000000000000000) := by
  have hk1 : kappa q ≤ 0.610230133555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501759314718 : ℝ)) (s := (0.865007277481 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612180299492 : ℝ) ≤ 0.686410557100 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612180299492 : ℝ)) (Q := (0.612180299492 : ℝ))
      (s := (0.790718205756 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781426233852 : ℝ)) (R := (0.781976091313 : ℝ)) (Q2 := (0.612180299492 : ℝ)) (T := (0.828968513070 : ℝ))
    (B := ((1376783438015049/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500564293303/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439120162359821/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609431900999 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500564293303 : ℝ)) (s := (0.865699363677 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611380598889 : ℝ) ≤ 0.685840910942 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611380598889 : ℝ)) (Q := (0.611380598889 : ℝ))
      (s := (0.791336694020 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780915313204 : ℝ)) (R := (0.781465170665 : ℝ)) (Q2 := (0.611380598889 : ℝ)) (T := (0.828624464791 : ℝ))
    (B := ((3439120162359821/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31210579493/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (137451395235117/200000000000000) := by
  have hk1 : kappa q ≤ 0.608634208992 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499369271888 : ℝ)) (s := (0.866389248718 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610581439460 : ℝ) ≤ 0.685271922048 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610581439460 : ℝ)) (Q := (0.610581439460 : ℝ))
      (s := (0.791953474510 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780404404389 : ℝ)) (R := (0.780954261850 : ℝ)) (Q2 := (0.610581439460 : ℝ)) (T := (0.828280670817 : ℝ))
    (B := ((137451395235117/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498174250473/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866905491148059/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607837056941 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498174250473 : ℝ)) (s := (0.867076937859 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609782820613 : ℝ) ≤ 0.684703589206 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609782820613 : ℝ)) (Q := (0.609782820613 : ℝ))
      (s := (0.792568553304 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779893507050 : ℝ)) (R := (0.780443364511 : ℝ)) (Q2 := (0.609782820613 : ℝ)) (T := (0.827937130730 : ℝ))
    (B := ((6866905491148059/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (248489614529/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (26801748058197/39062500000000) := by
  have hk1 : kappa q ≤ 0.607040444253 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496979229058 : ℝ)) (s := (0.867762436319 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608984741752 : ℝ) ≤ 0.684135911205 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608984741752 : ℝ)) (Q := (0.608984741752 : ℝ))
      (s := (0.793181936452 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779382620829 : ℝ)) (R := (0.779932478290 : ℝ)) (Q2 := (0.608984741752 : ℝ)) (T := (0.827593844116 : ℝ))
    (B := ((26801748058197/39062500000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495784207643/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855595787046871/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606244370339 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495784207643 : ℝ)) (s := (0.868445749286 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608187202290 : ℝ) ≤ 0.683568886844 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608187202290 : ℝ)) (Q := (0.608187202290 : ℝ))
      (s := (0.793793629964 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778871745371 : ℝ)) (R := (0.779421602832 : ℝ)) (Q2 := (0.608187202290 : ℝ)) (T := (0.827250810563 : ℝ))
    (B := ((6855595787046871/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494589186227/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849950333670801/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605448834612 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494589186227 : ℝ)) (s := (0.869126881916 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607390201635 : ℝ) ≤ 0.683002514917 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607390201635 : ℝ)) (Q := (0.607390201635 : ℝ))
      (s := (0.794403639820 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778360880318 : ℝ)) (R := (0.778910737779 : ℝ)) (Q2 := (0.607390201635 : ℝ)) (T := (0.826908029656 : ℝ))
    (B := ((6849950333670801/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123348541203/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (342215556644247/500000000000000) := by
  have hk1 : kappa q ≤ 0.604653836492 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493394164812 : ℝ)) (s := (0.869805839329 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606593739210 : ℝ) ≤ 0.682436794232 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606593739210 : ℝ)) (Q := (0.606593739210 : ℝ))
      (s := (0.795011971955 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777850025320 : ℝ)) (R := (0.778399882781 : ℝ)) (Q2 := (0.606593739210 : ℝ)) (T := (0.826565500987 : ℝ))
    (B := ((342215556644247/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492199143397/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1367735634968217/2000000000000000) := by
  have hk1 : kappa q ≤ 0.603859375398 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492199143397 : ℝ)) (s := (0.870482626616 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605797814429 : ℝ) ≤ 0.681871723595 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605797814429 : ℝ)) (Q := (0.605797814429 : ℝ))
      (s := (0.795618632282 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777339180021 : ℝ)) (R := (0.777889037482 : ℝ)) (Q2 := (0.605797814429 : ℝ)) (T := (0.826223224146 : ℝ))
    (B := ((1367735634968217/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245502060991/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6833051449727887/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603065450753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491004121982 : ℝ)) (s := (0.871157248835 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605002426716 : ℝ) ≤ 0.681307301818 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605002426716 : ℝ)) (Q := (0.605002426716 : ℝ))
      (s := (0.796223626671 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776828344070 : ℝ)) (R := (0.777378201531 : ℝ)) (Q2 := (0.605002426716 : ℝ)) (T := (0.825881198727 : ℝ))
    (B := ((6833051449727887/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489809100567/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827430947770643/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602272061985 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489809100567 : ℝ)) (s := (0.871829711012 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604207575498 : ℝ) ≤ 0.680743527718 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604207575498 : ℝ)) (Q := (0.604207575498 : ℝ))
      (s := (0.796826960959 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776317517117 : ℝ)) (R := (0.776867374578 : ℝ)) (Q2 := (0.604207575498 : ℝ)) (T := (0.825539424326 : ℝ))
    (B := ((6827430947770643/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30538379947/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821816659231071/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601479208524 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488614079152 : ℝ)) (s := (0.872500018141 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603413260204 : ℝ) ≤ 0.680180400117 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603413260204 : ℝ)) (Q := (0.603413260204 : ℝ))
      (s := (0.797428640952 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775806698812 : ℝ)) (R := (0.776356556273 : ℝ)) (Q2 := (0.603413260204 : ℝ)) (T := (0.825197900538 : ℝ))
    (B := ((6821816659231071/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487419057737/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3408104287203553/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600686889801 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487419057737 : ℝ)) (s := (0.873168175185 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602619480264 : ℝ) ≤ 0.679617917839 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602619480264 : ℝ)) (Q := (0.602619480264 : ℝ))
      (s := (0.798028672422 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775295888805 : ℝ)) (R := (0.775845746266 : ℝ)) (Q2 := (0.602619480264 : ℝ)) (T := (0.824856626962 : ℝ))
    (B := ((3408104287203553/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243112018161/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702651670908171/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599895105253 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486224036322 : ℝ)) (s := (0.873834187076 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601826235113 : ℝ) ≤ 0.679056079712 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601826235113 : ℝ)) (Q := (0.601826235113 : ℝ))
      (s := (0.798627061106 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774785086750 : ℝ)) (R := (0.775334944211 : ℝ)) (Q2 := (0.601826235113 : ℝ)) (T := (0.824515603197 : ℝ))
    (B := ((1702651670908171/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485029014907/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6805010977277531/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599103854321 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485029014907 : ℝ)) (s := (0.874498058717 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601033524193 : ℝ) ≤ 0.678494884573 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601033524193 : ℝ)) (Q := (0.601033524193 : ℝ))
      (s := (0.799223812706 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774274292301 : ℝ)) (R := (0.774824149762 : ℝ)) (Q2 := (0.601033524193 : ℝ)) (T := (0.824174828846 : ℝ))
    (B := ((6805010977277531/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120958498373/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799421445746959/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598313136444 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483833993492 : ℝ)) (s := (0.875159794976 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600241346940 : ℝ) ≤ 0.677934331256 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600241346940 : ℝ)) (Q := (0.600241346940 : ℝ))
      (s := (0.799818932899 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773763505111 : ℝ)) (R := (0.774313362572 : ℝ)) (Q2 := (0.600241346940 : ℝ)) (T := (0.823834303512 : ℝ))
    (B := ((6799421445746959/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482638972077/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793838079481659/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597522951070 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482638972077 : ℝ)) (s := (0.875819400695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599449702802 : ℝ) ≤ 0.677374418607 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599449702802 : ℝ)) (Q := (0.599449702802 : ℝ))
      (s := (0.800412427322 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773252724837 : ℝ)) (R := (0.773802582298 : ℝ)) (Q2 := (0.599449702802 : ℝ)) (T := (0.823494026801 : ℝ))
    (B := ((6793838079481659/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240721975331/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3394130434478747/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596733297645 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481443950662 : ℝ)) (s := (0.876476880683 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598658591223 : ℝ) ≤ 0.676815145470 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598658591223 : ℝ)) (Q := (0.598658591223 : ℝ))
      (s := (0.801004301584 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772741951134 : ℝ)) (R := (0.773291808595 : ℝ)) (Q2 := (0.598658591223 : ℝ)) (T := (0.823153998318 : ℝ))
    (B := ((3394130434478747/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240124464623/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (135653772989087/200000000000000) := by
  have hk1 : kappa q ≤ 0.595944175623 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480248929246 : ℝ)) (s := (0.877132239722 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597868011657 : ℝ) ≤ 0.676256510697 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597868011657 : ℝ)) (Q := (0.597868011657 : ℝ))
      (s := (0.801594561258 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772231183662 : ℝ)) (R := (0.772781041123 : ℝ)) (Q2 := (0.597868011657 : ℝ)) (T := (0.822814217673 : ℝ))
    (B := ((135653772989087/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479053907831/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1355424506022449/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595155584457 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479053907831 : ℝ)) (s := (0.877785482560 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597077963557 : ℝ) ≤ 0.675698513143 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597077963557 : ℝ)) (Q := (0.597077963557 : ℝ))
      (s := (0.802183211888 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771720422080 : ℝ)) (R := (0.772270279541 : ℝ)) (Q2 := (0.597077963557 : ℝ)) (T := (0.822474684476 : ℝ))
    (B := ((1355424506022449/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12600 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (29866180401/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385781270382513/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594367523605 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477858886416 : ℝ)) (s := (0.878436613919 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596288446377 : ℝ) ≤ 0.675141151666 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596288446377 : ℝ)) (Q := (0.596288446377 : ℝ))
      (s := (0.802770258990 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771209666046 : ℝ)) (R := (0.771759523507 : ℝ)) (Q2 := (0.596288446377 : ℝ)) (T := (0.822135398339 : ℝ))
    (B := ((3385781270382513/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S10
namespace BstLean.Part269.S10
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12600 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052694435119 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S10.wn_upper (by omega : 12600 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010639113969 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035952292573)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010639113969 + 2 * 0.737676 / 12600) := by gcongr
    _ ≤ (0.052694435119 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12600 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12600 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.249721603218 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12600 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.249721603218 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12600 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003617997022 + 0.003320722551 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003617997022 + 0.003320722551 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.249721603218 ≤ R)
    (hB : (X + 0.052694435119 + R + 0.008515159490) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008515159490 := by
    convert (BstLean.Part269.S10.finite_centre_upper (by omega : 12600 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (21428776841/250000000000)
  | 2 => (86662061419/1000000000000)
  | 3 => (17521556067/200000000000)
  | 4 => (88553825341/1000000000000)
  | 5 => (5593879997/62500000000)
  | 6 => (90454797199/1000000000000)
  | 7 => (22853662797/250000000000)
  | 8 => (9238479301/100000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003617997022 + 0.003320722551 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219340857256 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011009982573 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003617997022 + 0.003320722551 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220910170128 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011125405175 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003617997022 + 0.003320722551 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222459020650 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011240446546 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003617997022 + 0.003320722551 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223987616182 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011355115042 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003617997022 + 0.003320722551 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225496158906 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011469418783 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003617997022 + 0.003320722551 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226984844343 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011583365535 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003617997022 + 0.003320722551 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228453863222 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011696962853 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12600 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003617997022 + 0.003320722551 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229903400021 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011810217970 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12600 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g) :
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

end BstLean.Part269.S10

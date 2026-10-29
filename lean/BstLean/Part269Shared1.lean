import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S1
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12375 ≤ n) : wn n ≤ 1.036280558322 := by
  have hnR : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.242977306434 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.242977306434 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036280558322 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12375 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12375 + 24 / (12375 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12375 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008592557093 : ℝ) := by
  have hnR : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.242977306434 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12375 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036280558322 * (81 / 1000 / 12375)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036280558322 * n *
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
        4 * (1 / 2.506628) * 1.036280558322 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036280558322 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036280558322 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12375)) / 111.242977306434 := by gcongr
    _ ≤ (0.008592557093 : ℝ) := by norm_num

end BstLean.Part269.S1
namespace BstLean.Part269.S1
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12375 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12375 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12375 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12375 + 0.008592557093 / 111.242977306434) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12375 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12375 := by gcongr
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
  have hn : (111.242977306434 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S1.finite_centre_upper (by omega : 12375 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264012573167/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010888323534619/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627912540877 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528025146334 : ℝ)) (s := (0.849228735289 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629918240431 : ℝ) ≤ 0.699116152619 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629918240431 : ℝ)) (Q := (0.629918240431 : ℝ))
      (s := (0.776661451582 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792664229849 : ℝ)) (R := (0.793224084718 : ℝ)) (Q2 := (0.629918240431 : ℝ)) (T := (0.836605520261 : ℝ))
    (B := ((7010888323534619/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526827660967/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502528914750743/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627100600662 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526827660967 : ℝ)) (s := (0.849972126391 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629104804817 : ℝ) ≤ 0.698530525451 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629104804817 : ℝ)) (Q := (0.629104804817 : ℝ))
      (s := (0.777320490246 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792151905298 : ℝ)) (R := (0.792711760167 : ℝ)) (Q2 := (0.629104804817 : ℝ)) (T := (0.836255048051 : ℝ))
    (B := ((3502528914750743/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1314075439/2500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (699923389607527/1000000000000000) := by
  have hk1 : kappa q ≤ 0.626289217154 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525630175600 : ℝ)) (s := (0.850713182277 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628291926564 : ℝ) ≤ 0.697945586124 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628291926564 : ℝ)) (Q := (0.628291926564 : ℝ))
      (s := (0.777977669998 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791639600803 : ℝ)) (R := (0.792199455672 : ℝ)) (Q2 := (0.628291926564 : ℝ)) (T := (0.835904840799 : ℝ))
    (B := ((699923389607527/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262216345117/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6993416512255249/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625478389687 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524432690234 : ℝ)) (s := (0.851451909044 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627479605003 : ℝ) ≤ 0.697361333322 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627479605003 : ℝ)) (Q := (0.627479605003 : ℝ))
      (s := (0.778632997828 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791127315981 : ℝ)) (R := (0.791687170850 : ℝ)) (Q2 := (0.627479605003 : ℝ)) (T := (0.835554898050 : ℝ))
    (B := ((6993416512255249/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523235204867/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (698760566708453/1000000000000000) := by
  have hk1 : kappa q ≤ 0.624668117595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523235204867 : ℝ)) (s := (0.852188312751 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667839471 : ℝ) ≤ 0.696777765740 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667839471 : ℝ)) (Q := (0.626667839471 : ℝ))
      (s := (0.779286480682 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790615050451 : ℝ)) (R := (0.791174905320 : ℝ)) (Q2 := (0.626667839471 : ℝ)) (T := (0.835205219354 : ℝ))
    (B := ((698760566708453/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1044075439/2000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (279272053985991/400000000000000) := by
  have hk1 : kappa q ≤ 0.623858400218 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522037719500 : ℝ)) (s := (0.852922399413 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625856629304 : ℝ) ≤ 0.696194882073 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625856629304 : ℝ)) (Q := (0.625856629304 : ℝ))
      (s := (0.779938125467 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790102803832 : ℝ)) (R := (0.790662658701 : ℝ)) (Q2 := (0.625856629304 : ℝ)) (T := (0.834855804260 : ℝ))
    (B := ((279272053985991/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (260420117067/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3488001774540461/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623049236897 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520840234134 : ℝ)) (s := (0.853654175008 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625045973842 : ℝ) ≤ 0.695612681018 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625045973842 : ℝ)) (Q := (0.625045973842 : ℝ))
      (s := (0.780587939046 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789590575743 : ℝ)) (R := (0.790150430612 : ℝ)) (Q2 := (0.625045973842 : ℝ)) (T := (0.834506652319 : ℝ))
    (B := ((3488001774540461/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519642748767/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (174255306363773/250000000000000) := by
  have hk1 : kappa q ≤ 0.622240626976 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519642748767 : ℝ)) (s := (0.854383645475 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624235872429 : ℝ) ≤ 0.695031161281 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624235872429 : ℝ)) (Q := (0.624235872429 : ℝ))
      (s := (0.781235928240 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789078365805 : ℝ)) (R := (0.789638220674 : ℝ)) (Q2 := (0.624235872429 : ℝ)) (T := (0.834157763083 : ℝ))
    (B := ((174255306363773/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2592226317/5000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392885491055091/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621432569803 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518445263400 : ℝ)) (s := (0.855110816713 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623426324409 : ℝ) ≤ 0.694450321567 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623426324409 : ℝ)) (Q := (0.623426324409 : ℝ))
      (s := (0.781882099830 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788566173639 : ℝ)) (R := (0.789126028508 : ℝ)) (Q2 := (0.623426324409 : ℝ)) (T := (0.833809136106 : ℝ))
    (B := ((1392885491055091/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258623889017/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958649140512683/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620625064731 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517247778034 : ℝ)) (s := (0.855835694581 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622617329138 : ℝ) ≤ 0.693870160591 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622617329138 : ℝ)) (Q := (0.622617329138 : ℝ))
      (s := (0.782526460548 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788053998871 : ℝ)) (R := (0.788613853740 : ℝ)) (Q2 := (0.622617329138 : ℝ)) (T := (0.833460770944 : ℝ))
    (B := ((6958649140512683/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516050292667/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952877299562969/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619818111111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516050292667 : ℝ)) (s := (0.856558284905 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621808885962 : ℝ) ≤ 0.693290677065 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621808885962 : ℝ)) (Q := (0.621808885962 : ℝ))
      (s := (0.783169017096 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787541841121 : ℝ)) (R := (0.788101695990 : ℝ)) (Q2 := (0.621808885962 : ℝ)) (T := (0.833112667152 : ℝ))
    (B := ((6952877299562969/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5148528073/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473555960884311/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619011708302 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514852807300 : ℝ)) (s := (0.857278593467 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621000994241 : ℝ) ≤ 0.692711869712 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621000994241 : ℝ)) (Q := (0.621000994241 : ℝ))
      (s := (0.783809776127 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787029700016 : ℝ)) (R := (0.787589554885 : ℝ)) (Q2 := (0.621000994241 : ℝ)) (T := (0.832764824291 : ℝ))
    (B := ((3473555960884311/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256827660967/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3470676498256817/5000000000000000) := by
  have hk1 : kappa q ≤ 0.618205855665 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513655321934 : ℝ)) (s := (0.857996626013 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620193653334 : ℝ) ≤ 0.692133737255 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620193653334 : ℝ)) (Q := (0.620193653334 : ℝ))
      (s := (0.784448744256 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786517575182 : ℝ)) (R := (0.787077430051 : ℝ)) (Q2 := (0.620193653334 : ℝ)) (T := (0.832417241919 : ℝ))
    (B := ((3470676498256817/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512457836567/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935600513223427/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617400552561 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512457836567 : ℝ)) (s := (0.858712388255 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619386862601 : ℝ) ≤ 0.691556278420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619386862601 : ℝ)) (Q := (0.619386862601 : ℝ))
      (s := (0.785085928060 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786005466244 : ℝ)) (R := (0.786565321113 : ℝ)) (Q2 := (0.619386862601 : ℝ)) (T := (0.832069919597 : ℝ))
    (B := ((6935600513223427/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (639075439/1250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (433115903835287/625000000000000) := by
  have hk1 : kappa q ≤ 0.616595798358 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511260351200 : ℝ)) (s := (0.859425885863 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618580621411 : ℝ) ≤ 0.690979491944 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618580621411 : ℝ)) (Q := (0.618580621411 : ℝ))
      (s := (0.785721334072 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785493372832 : ℝ)) (R := (0.786053227701 : ℝ)) (Q2 := (0.618580621411 : ℝ)) (T := (0.831722856890 : ℝ))
    (B := ((433115903835287/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255031432917/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6924114830444641/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615791592427 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510062865834 : ℝ)) (s := (0.860137124474 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617774929130 : ℝ) ≤ 0.690403376561 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617774929130 : ℝ)) (Q := (0.617774929130 : ℝ))
      (s := (0.786354968789 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784981294574 : ℝ)) (R := (0.785541149443 : ℝ)) (Q2 := (0.617774929130 : ℝ)) (T := (0.831376053361 : ℝ))
    (B := ((6924114830444641/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508865380467/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918381610011753/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614987934139 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508865380467 : ℝ)) (s := (0.860846109687 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616969785131 : ℝ) ≤ 0.689827931012 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616969785131 : ℝ)) (Q := (0.616969785131 : ℝ))
      (s := (0.786986838668 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784469231101 : ℝ)) (R := (0.785029085970 : ℝ)) (Q2 := (0.616969785131 : ℝ)) (T := (0.831029508576 : ℝ))
    (B := ((6918381610011753/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5076678951/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1728163697413631/2500000000000000) := by
  have hk1 : kappa q ≤ 0.614184822871 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507667895100 : ℝ)) (s := (0.861552847065 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616165188788 : ℝ) ≤ 0.689253154042 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616165188788 : ℝ)) (Q := (0.616165188788 : ℝ))
      (s := (0.787616950127 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783957182042 : ℝ)) (R := (0.784517036911 : ℝ)) (Q2 := (0.616165188788 : ℝ)) (T := (0.830683222103 : ℝ))
    (B := ((1728163697413631/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506470409733/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (276277374360069/400000000000000) := by
  have hk1 : kappa q ≤ 0.613382258002 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506470409733 : ℝ)) (s := (0.862257342135 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615361139480 : ℝ) ≤ 0.688679044400 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615361139480 : ℝ)) (Q := (0.615361139480 : ℝ))
      (s := (0.788245309544 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783445147031 : ℝ)) (R := (0.784005001900 : ℝ)) (Q2 := (0.615361139480 : ℝ)) (T := (0.830337193511 : ℝ))
    (B := ((276277374360069/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505272924367/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450610153861027/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612580238915 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505272924367 : ℝ)) (s := (0.862959600388 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614557636589 : ℝ) ≤ 0.688105600842 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614557636589 : ℝ)) (Q := (0.614557636589 : ℝ))
      (s := (0.788871923262 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782933125701 : ℝ)) (R := (0.783492980570 : ℝ)) (Q2 := (0.614557636589 : ℝ)) (T := (0.829991422372 : ℝ))
    (B := ((3450610153861027/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504075439/1000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1723878156380973/2500000000000000) := by
  have hk1 : kappa q ≤ 0.611778764995 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504075439000 : ℝ)) (s := (0.863659627283 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613754679497 : ℝ) ≤ 0.687532822123 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613754679497 : ℝ)) (Q := (0.613754679497 : ℝ))
      (s := (0.789496797585 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782421117685 : ℝ)) (R := (0.782980972554 : ℝ)) (Q2 := (0.613754679497 : ℝ)) (T := (0.829645908257 : ℝ))
    (B := ((1723878156380973/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502877953633/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889811302155069/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610977835629 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502877953633 : ℝ)) (s := (0.864357428238 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612952267592 : ℝ) ≤ 0.686960707006 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612952267592 : ℝ)) (Q := (0.612952267592 : ℝ))
      (s := (0.790119938778 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781909122618 : ℝ)) (R := (0.782468977487 : ℝ)) (Q2 := (0.612952267592 : ℝ)) (T := (0.829300650740 : ℝ))
    (B := ((6889811302155069/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501680468267/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884116327402619/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610177450213 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501680468267 : ℝ)) (s := (0.865053008642 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612150400269 : ℝ) ≤ 0.686389254259 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612150400269 : ℝ)) (Q := (0.612150400269 : ℝ))
      (s := (0.790741353068 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781397140139 : ℝ)) (R := (0.781956995008 : ℝ)) (Q2 := (0.612150400269 : ℝ)) (T := (0.828955649398 : ℝ))
    (B := ((6884116327402619/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5004829829/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878427691092549/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609377608138 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500482982900 : ℝ)) (s := (0.865746373847 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611349076917 : ℝ) ≤ 0.685818462651 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611349076917 : ℝ)) (Q := (0.611349076917 : ℝ))
      (s := (0.791361046649 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780885169883 : ℝ)) (R := (0.781445024752 : ℝ)) (Q2 := (0.611349076917 : ℝ)) (T := (0.828610903807 : ℝ))
    (B := ((6878427691092549/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499285497533/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872745383089599/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608578308804 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499285497533 : ℝ)) (s := (0.866437529170 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610548296933 : ℝ) ≤ 0.685248330955 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610548296933 : ℝ)) (Q := (0.610548296933 : ℝ))
      (s := (0.791979025677 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780373211488 : ℝ)) (R := (0.780933066357 : ℝ)) (Q2 := (0.610548296933 : ℝ)) (T := (0.828266413546 : ℝ))
    (B := ((6872745383089599/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498088012167/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6867069393297017/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607779551613 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498088012167 : ℝ)) (s := (0.867126479896 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609748059721 : ℝ) ≤ 0.684678857955 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609748059721 : ℝ)) (Q := (0.609748059721 : ℝ))
      (s := (0.792595296269 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779861264596 : ℝ)) (R := (0.780421119465 : ℝ)) (Q2 := (0.609748059721 : ℝ)) (T := (0.827922178198 : ℝ))
    (B := ((6867069393297017/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1242226317/2500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861399711656323/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606981335968 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496890526800 : ℝ)) (s := (0.867813231276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608948364683 : ℝ) ≤ 0.684110042432 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608948364683 : ℝ)) (Q := (0.608948364683 : ℝ))
      (s := (0.793209864507 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779349328846 : ℝ)) (R := (0.779909183715 : ℝ)) (Q2 := (0.608948364683 : ℝ)) (T := (0.827578197343 : ℝ))
    (B := ((6861399711656323/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495693041433/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855736328147083/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606183661277 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495693041433 : ℝ)) (s := (0.868497788527 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608149211225 : ℝ) ≤ 0.683541883174 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608149211225 : ℝ)) (Q := (0.608149211225 : ℝ))
      (s := (0.793822736439 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778837403880 : ℝ)) (R := (0.779397258749 : ℝ)) (Q2 := (0.608149211225 : ℝ)) (T := (0.827234470565 : ℝ))
    (B := ((6855736328147083/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494495556067/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3425039616393341/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605386526952 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494495556067 : ℝ)) (s := (0.869180156832 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607350598755 : ℝ) ≤ 0.682974378972 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607350598755 : ℝ)) (Q := (0.607350598755 : ℝ))
      (s := (0.794433918078 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778325489340 : ℝ)) (R := (0.778885344209 : ℝ)) (Q2 := (0.607350598755 : ℝ)) (T := (0.826890997450 : ℝ))
    (B := ((3425039616393341/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4932980707/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422214207815051/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604589932406 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493298070700 : ℝ)) (s := (0.869860341345 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606552526690 : ℝ) ≤ 0.682407528626 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606552526690 : ℝ)) (Q := (0.606552526690 : ℝ))
      (s := (0.795043415397 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777813584872 : ℝ)) (R := (0.778373439741 : ℝ)) (Q2 := (0.606552526690 : ℝ)) (T := (0.826547777587 : ℝ))
    (B := ((3422214207815051/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492100585333/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (213711995836553/312500000000000) := by
  have hk1 : kappa q ≤ 0.603793877055 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492100585333 : ℝ)) (s := (0.870538347183 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605754994442 : ℝ) ≤ 0.681841330933 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605754994442 : ℝ)) (Q := (0.605754994442 : ℝ))
      (s := (0.795651234342 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777301690118 : ℝ)) (R := (0.777861544987 : ℝ)) (Q2 := (0.605754994442 : ℝ)) (T := (0.826204810563 : ℝ))
    (B := ((213711995836553/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (490903099967/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6833145576334967/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602998360322 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490903099967 : ℝ)) (s := (0.871214179432 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604958001432 : ℝ) ≤ 0.681275784700 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604958001432 : ℝ)) (Q := (0.604958001432 : ℝ))
      (s := (0.796257380816 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776789804726 : ℝ)) (R := (0.777349659595 : ℝ)) (Q2 := (0.604958001432 : ℝ)) (T := (0.825862095970 : ℝ))
    (B := ((6833145576334967/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2448528073/5000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1365502706898471/2000000000000000) := by
  have hk1 : kappa q ≤ 0.602203381628 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489705614600 : ℝ)) (s := (0.871887843148 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604161547083 : ℝ) ≤ 0.680710888736 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604161547083 : ℝ)) (Q := (0.604161547083 : ℝ))
      (s := (0.796861860693 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776277928343 : ℝ)) (R := (0.776837783212 : ℝ)) (Q2 := (0.604161547083 : ℝ)) (T := (0.825519633400 : ℝ))
    (B := ((1365502706898471/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488508129233/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821887731445013/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601408940401 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488508129233 : ℝ)) (s := (0.872559343354 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603365630820 : ℝ) ≤ 0.680146641856 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603365630820 : ℝ)) (Q := (0.603365630820 : ℝ))
      (s := (0.797464679811 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775766060617 : ℝ)) (R := (0.776325915486 : ℝ)) (Q2 := (0.603365630820 : ℝ)) (T := (0.825177422447 : ℝ))
    (B := ((6821887731445013/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487310643867/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1363253631486519/2000000000000000) := by
  have hk1 : kappa q ≤ 0.600615036071 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487310643867 : ℝ)) (s := (0.873228685039 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602570252073 : ℝ) ≤ 0.679583042879 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602570252073 : ℝ)) (Q := (0.602570252073 : ℝ))
      (s := (0.798065843974 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775254201198 : ℝ)) (R := (0.775814056067 : ℝ)) (Q2 := (0.602570252073 : ℝ)) (T := (0.824835462709 : ℝ))
    (B := ((1363253631486519/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (972226317/2000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702663700682761/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599821668069 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486113158500 : ℝ)) (s := (0.873895873165 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601775410272 : ℝ) ≤ 0.679020090624 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601775410272 : ℝ)) (Q := (0.601775410272 : ℝ))
      (s := (0.798665358954 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774742349736 : ℝ)) (R := (0.775302204605 : ℝ)) (Q2 := (0.601775410272 : ℝ)) (T := (0.824493753781 : ℝ))
    (B := ((1702663700682761/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484915673133/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6805047657652377/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599028835832 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484915673133 : ℝ)) (s := (0.874560912659 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600981104851 : ℝ) ≤ 0.678457783920 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600981104851 : ℝ)) (Q := (0.600981104851 : ℝ))
      (s := (0.799263230490 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774230505881 : ℝ)) (R := (0.774790360750 : ℝ)) (Q2 := (0.600981104851 : ℝ)) (T := (0.824152295263 : ℝ))
    (B := ((6805047657652377/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483718187767/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799446712544477/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598236538800 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483718187767 : ℝ)) (s := (0.875223808419 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600187335250 : ℝ) ≤ 0.677896121597 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600187335250 : ℝ)) (Q := (0.600187335250 : ℝ))
      (s := (0.799859464285 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773718669288 : ℝ)) (R := (0.774278524157 : ℝ)) (Q2 := (0.600187335250 : ℝ)) (T := (0.823811086756 : ℝ))
    (B := ((6799446712544477/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (301575439/625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3396925978895443/5000000000000000) := by
  have hk1 : kappa q ≤ 0.597444776414 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482520702400 : ℝ)) (s := (0.875884565315 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599394100909 : ℝ) ≤ 0.677335102492 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599394100909 : ℝ)) (Q := (0.599394100909 : ℝ))
      (s := (0.800454066013 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773206839609 : ℝ)) (R := (0.773766694478 : ℝ)) (Q2 := (0.599394100909 : ℝ)) (T := (0.823470127865 : ℝ))
    (B := ((3396925978895443/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481323217033/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1697065845952649/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596653548119 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481323217033 : ℝ)) (s := (0.876543188181 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598601401274 : ℝ) ≤ 0.676774725444 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598601401274 : ℝ)) (Q := (0.598601401274 : ℝ))
      (s := (0.801047041311 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772695016500 : ℝ)) (R := (0.773254871369 : ℝ)) (Q2 := (0.598601401274 : ℝ)) (T := (0.823129418192 : ℝ))
    (B := ((1697065845952649/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480125731667/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782680312458917/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595862853364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480125731667 : ℝ)) (s := (0.877199681824 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597809235791 : ℝ) ≤ 0.676214989297 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597809235791 : ℝ)) (Q := (0.597809235791 : ℝ))
      (s := (0.801638395789 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772183199616 : ℝ)) (R := (0.772743054485 : ℝ)) (Q2 := (0.597809235791 : ℝ)) (T := (0.822788957345 : ℝ))
    (B := ((6782680312458917/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4789282463/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1694275711470651/2500000000000000) := by
  have hk1 : kappa q ≤ 0.595072691601 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478928246300 : ℝ)) (s := (0.877854051023 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597017603910 : ℝ) ≤ 0.675655892899 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597017603910 : ℝ)) (Q := (0.597017603910 : ℝ))
      (s := (0.802228135023 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771671388614 : ℝ)) (R := (0.772231243483 : ℝ)) (Q2 := (0.597017603910 : ℝ)) (T := (0.822448744931 : ℝ))
    (B := ((1694275711470651/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12375 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477730760933/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771531534243303/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594283062283 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477730760933 : ℝ)) (s := (0.878506300523 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596226505084 : ℝ) ≤ 0.675097435102 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596226505084 : ℝ)) (Q := (0.596226505084 : ℝ))
      (s := (0.802816264556 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771159583152 : ℝ)) (R := (0.771719438021 : ℝ)) (Q2 := (0.596226505084 : ℝ)) (T := (0.822108780559 : ℝ))
    (B := ((6771531534243303/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S1
namespace BstLean.Part269.S1
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12375 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.053176555851 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S1.wn_upper (by omega : 12375 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010735397506 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036280558322)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010735397506 + 2 * 0.737676 / 12375) := by gcongr
    _ ≤ (0.053176555851 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12375 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12375 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.242977306434 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12375 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.242977306434 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12375 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.004098049004 + 0.003383255859 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004098049004 + 0.003383255859 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.242977306434 ≤ R)
    (hB : (X + 0.053176555851 + R + 0.008592557093) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008592557093 := by
    convert (BstLean.Part269.S1.finite_centre_upper (by omega : 12375 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (21605670133/250000000000)
  | 2 => (21845965947/250000000000)
  | 3 => (88346080131/1000000000000)
  | 4 => (44655698981/500000000000)
  | 5 => (90282294831/1000000000000)
  | 6 => (45630857479/500000000000)
  | 7 => (46126565793/500000000000)
  | 8 => (11657576763/125000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.004098049004 + 0.003383255859 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011109622455 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.004098049004 + 0.003383255859 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011226089627 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.004098049004 + 0.003383255859 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011342172117 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.004098049004 + 0.003383255859 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011457878359 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.004098049004 + 0.003383255859 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011573216544 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.004098049004 + 0.003383255859 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011688194509 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.004098049004 + 0.003383255859 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011802819878 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12375 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.004098049004 + 0.003383255859 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011917099949 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12375 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g) :
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

end BstLean.Part269.S1

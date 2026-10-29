import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S8
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12550 ≤ n) : wn n ≤ 1.036024472514 := by
  have hnR : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.026782512040 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.026782512040 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036024472514 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12550 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12550 + 24 / (12550 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12550 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008532178410 : ℝ) := by
  have hnR : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.026782512040 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12550 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036024472514 * (81 / 1000 / 12550)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036024472514 * n *
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
        4 * (1 / 2.506628) * 1.036024472514 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036024472514 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036024472514 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12550)) / 112.026782512040 := by gcongr
    _ ≤ (0.008532178410 : ℝ) := by norm_num

end BstLean.Part269.S8
namespace BstLean.Part269.S8
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12550 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12550 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12550 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12550 + 0.008532178410 / 112.026782512040) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12550 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12550 := by gcongr
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
  have hn : (112.026782512040 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S8.finite_centre_upper (by omega : 12550 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264022184389/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (876315662371327/1250000000000000) := by
  have hk1 : kappa q ≤ 0.627925578962 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528044368778 : ℝ)) (s := (0.849216783043 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629913259070 : ℝ) ≤ 0.699112565450 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629913259070 : ℝ)) (Q := (0.629913259070 : ℝ))
      (s := (0.776665491733 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792668900196 : ℝ)) (R := (0.793220948324 : ℝ)) (Q2 := (0.629913259070 : ℝ)) (T := (0.836603373944 : ℝ))
    (B := ((876315662371327/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65856100707/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1400940889166109/2000000000000000) := by
  have hk1 : kappa q ≤ 0.627114932728 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526848805656 : ℝ)) (s := (0.849959020177 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629101127818 : ℝ) ≤ 0.698527878874 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629101127818 : ℝ)) (Q := (0.629101127818 : ℝ))
      (s := (0.777323466119 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792157395410 : ℝ)) (R := (0.792709443538 : ℝ)) (Q2 := (0.629101127818 : ℝ)) (T := (0.836253463857 : ℝ))
    (B := ((1400940889166109/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262826621267/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998890131964111/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626304841426 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525653242534 : ℝ)) (s := (0.850698929478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628289552151 : ℝ) ≤ 0.697943877938 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628289552151 : ℝ)) (Q := (0.628289552151 : ℝ))
      (s := (0.777979587559 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791645910620 : ℝ)) (R := (0.792197958748 : ℝ)) (Q2 := (0.628289552151 : ℝ)) (T := (0.835903817881 : ℝ))
    (B := ((6998890131964111/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131114419853/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496541173211943/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625495304394 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524457679412 : ℝ)) (s := (0.851436517015 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478531404 : ℝ) ≤ 0.697360561337 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478531404 : ℝ)) (Q := (0.627478531404 : ℝ))
      (s := (0.778633863011 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791134445445 : ℝ)) (R := (0.791686493573 : ℝ)) (Q2 := (0.627478531404 : ℝ)) (T := (0.835554435567 : ℝ))
    (B := ((3496541173211943/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52326211629/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1746820269576497/2500000000000000) := by
  have hk1 : kappa q ≤ 0.624686320971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523262116290 : ℝ)) (s := (0.852171788818 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668064915 : ℝ) ≤ 0.696777927770 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668064915 : ℝ)) (Q := (0.626668064915 : ℝ))
      (s := (0.779286299390 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790622999505 : ℝ)) (R := (0.791175047633 : ℝ)) (Q2 := (0.626668064915 : ℝ)) (T := (0.835205316464 : ℝ))
    (B := ((1746820269576497/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522066553167/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (698148631674981/1000000000000000) := by
  have hk1 : kappa q ≤ 0.623877890496 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522066553167 : ℝ)) (s := (0.852904750875 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625858152024 : ℝ) ≤ 0.696195975935 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625858152024 : ℝ)) (Q := (0.625858152024 : ℝ))
      (s := (0.779936903567 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790111572420 : ℝ)) (R := (0.790663620548 : ℝ)) (Q2 := (0.625858152024 : ℝ)) (T := (0.834856460123 : ℝ))
    (B := ((698148631674981/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (104174198009/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975698050937747/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623070012316 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520870990045 : ℝ)) (s := (0.853635409136 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625048792073 : ℝ) ≤ 0.695614704540 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625048792073 : ℝ)) (Q := (0.625048792073 : ℝ))
      (s := (0.780585682375 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789600163812 : ℝ)) (R := (0.790152211940 : ℝ)) (Q2 := (0.625048792073 : ℝ)) (T := (0.834507866099 : ℝ))
    (B := ((6975698050937747/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519675426923/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742479067523731/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622262685778 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519675426923 : ℝ)) (s := (0.854363769511 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624239984409 : ℝ) ≤ 0.695034112292 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624239984409 : ℝ)) (Q := (0.624239984409 : ℝ))
      (s := (0.781232642601 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789088773303 : ℝ)) (R := (0.789640821431 : ℝ)) (Q2 := (0.624239984409 : ℝ)) (T := (0.834159533943 : ℝ))
    (B := ((1742479067523731/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518479863801/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964140963488933/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621455910233 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518479863801 : ℝ)) (s := (0.855089837873 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623431728384 : ℝ) ≤ 0.694454197909 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623431728384 : ℝ)) (Q := (0.623431728384 : ℝ))
      (s := (0.781877790991 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788577400518 : ℝ)) (R := (0.789129448646 : ℝ)) (Q2 := (0.623431728384 : ℝ)) (T := (0.833811463216 : ℝ))
    (B := ((6964140963488933/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517284300679/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3479186060214783/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620649685035 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517284300679 : ℝ)) (s := (0.855813620055 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622624023349 : ℝ) ≤ 0.693874960105 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622624023349 : ℝ)) (Q := (0.622624023349 : ℝ))
      (s := (0.782521134251 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788066045081 : ℝ)) (R := (0.788618093209 : ℝ)) (Q2 := (0.622624023349 : ℝ)) (T := (0.833463653472 : ℝ))
    (B := ((3479186060214783/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129022184389/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (869076216283569/1250000000000000) := by
  have hk1 : kappa q ≤ 0.619844009541 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516088737556 : ℝ)) (s := (0.856535121854 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621816868661 : ℝ) ≤ 0.693296397605 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621816868661 : ℝ)) (Q := (0.621816868661 : ℝ))
      (s := (0.783162679045 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787554706618 : ℝ)) (R := (0.788106754746 : ℝ)) (Q2 := (0.621816868661 : ℝ)) (T := (0.833116104271 : ℝ))
    (B := ((869076216283569/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257446587217/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6946853782399299/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619038883111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514893174434 : ℝ)) (s := (0.857254349025 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621010263679 : ℝ) ≤ 0.692718509133 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621010263679 : ℝ)) (Q := (0.621010263679 : ℝ))
      (s := (0.783802431998 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787043384755 : ℝ)) (R := (0.787595432883 : ℝ)) (Q2 := (0.621010263679 : ℝ)) (T := (0.832768815173 : ℝ))
    (B := ((6946853782399299/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32106100707/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3470552133128317/5000000000000000) := by
  have hk1 : kappa q ≤ 0.618234305109 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513697611312 : ℝ)) (s := (0.857971307290 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620204207764 : ℝ) ≤ 0.692141293418 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620204207764 : ℝ)) (Q := (0.620204207764 : ℝ))
      (s := (0.784440399694 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786532079120 : ℝ)) (R := (0.787084127248 : ℝ)) (Q2 := (0.620204207764 : ℝ)) (T := (0.832421785740 : ℝ))
    (B := ((3470552133128317/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51250204819/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1733840292829137/2500000000000000) := by
  have hk1 : kappa q ≤ 0.617430274901 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512502048190 : ℝ)) (s := (0.858686002333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619398700282 : ℝ) ≤ 0.691564749197 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619398700282 : ℝ)) (Q := (0.619398700282 : ℝ))
      (s := (0.785076588678 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786020789341 : ℝ)) (R := (0.786572837469 : ℝ)) (Q2 := (0.619398700282 : ℝ)) (T := (0.832075015536 : ℝ))
    (B := ((1733840292829137/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127826621267/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929624487095943/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616626791856 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511306485068 : ℝ)) (s := (0.859398439799 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618593740600 : ℝ) ≤ 0.690988875206 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618593740600 : ℝ)) (Q := (0.618593740600 : ℝ))
      (s := (0.785711005454 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785509515048 : ℝ)) (R := (0.786061563176 : ℝ)) (Q2 := (0.618593740600 : ℝ)) (T := (0.831728504125 : ℝ))
    (B := ((6929624487095943/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102022184389/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923894203152383/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615823855347 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510110921945 : ℝ)) (s := (0.860108625299 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617789328092 : ℝ) ≤ 0.690413670189 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617789328092 : ℝ)) (Q := (0.617789328092 : ℝ))
      (s := (0.786343656486 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784998255872 : ℝ)) (R := (0.785550304000 : ℝ)) (Q2 := (0.617789328092 : ℝ)) (T := (0.831382251074 : ℝ))
    (B := ((6923894203152383/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508915358823/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (21619282215887/31250000000000) := by
  have hk1 : kappa q ≤ 0.615021464750 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508915358823 : ℝ)) (s := (0.860816564406 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616985462132 : ℝ) ≤ 0.689839132893 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616985462132 : ℝ)) (Q := (0.616985462132 : ℝ))
      (s := (0.786974548203 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784487011445 : ℝ)) (R := (0.785039059573 : ℝ)) (Q2 := (0.616985462132 : ℝ)) (T := (0.831036255952 : ℝ))
    (B := ((21619282215887/31250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507719795701/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912452794528451/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614219619445 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507719795701 : ℝ)) (s := (0.861522262657 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616182142097 : ℝ) ≤ 0.689265262068 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616182142097 : ℝ)) (Q := (0.616182142097 : ℝ))
      (s := (0.787603686991 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783975781399 : ℝ)) (R := (0.784527829527 : ℝ)) (Q2 := (0.616182142097 : ℝ)) (T := (0.830690518327 : ℝ))
    (B := ((6912452794528451/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506524232579/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906741649164273/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613418318812 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506524232579 : ℝ)) (s := (0.862225725556 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615379367368 : ℝ) ≤ 0.688692056470 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615379367368 : ℝ)) (Q := (0.615379367368 : ℝ))
      (s := (0.788231079201 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783464565368 : ℝ)) (R := (0.784016613496 : ℝ)) (Q2 := (0.615379367368 : ℝ)) (T := (0.830345037771 : ℝ))
    (B := ((6906741649164273/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505328669457/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450518431354519/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612617562238 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505328669457 : ℝ)) (s := (0.862926958569 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614577137330 : ℝ) ≤ 0.688119514858 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614577137330 : ℝ)) (Q := (0.614577137330 : ℝ))
      (s := (0.788856731145 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782953362987 : ℝ)) (R := (0.783505411115 : ℝ)) (Q2 := (0.614577137330 : ℝ)) (T := (0.829999813857 : ℝ))
    (B := ((3450518431354519/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252066553167/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895338424919917/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611817349109 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504133106334 : ℝ)) (s := (0.863625967129 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613775451370 : ℝ) ≤ 0.687547635996 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613775451370 : ℝ)) (Q := (0.613775451370 : ℝ))
      (s := (0.789480649096 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782442173892 : ℝ)) (R := (0.782994222020 : ℝ)) (Q2 := (0.613775451370 : ℝ)) (T := (0.829654846159 : ℝ))
    (B := ((6895338424919917/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125734385803/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889646325593277/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611017678820 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502937543212 : ℝ)) (s := (0.864322756630 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612974308878 : ℝ) ≤ 0.686976418651 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612974308878 : ℝ)) (Q := (0.612974308878 : ℝ))
      (s := (0.790102839291 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781930997720 : ℝ)) (R := (0.782483045848 : ℝ)) (Q2 := (0.612974308878 : ℝ)) (T := (0.829310134254 : ℝ))
    (B := ((6889646325593277/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50174198009/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1376792110912889/2000000000000000) := by
  have hk1 : kappa q ≤ 0.610218550763 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501741980090 : ℝ)) (s := (0.865017332437 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612173709248 : ℝ) ≤ 0.686405861597 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612173709248 : ℝ)) (Q := (0.612173709248 : ℝ))
      (s := (0.790723307932 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781419834109 : ℝ)) (R := (0.781971882237 : ℝ)) (Q2 := (0.612173709248 : ℝ)) (T := (0.828965677719 : ℝ))
    (B := ((1376792110912889/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62568302121/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878281101707479/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609419964337 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500546416968 : ℝ)) (s := (0.865709699877 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611373651876 : ℝ) ≤ 0.685835963608 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611373651876 : ℝ)) (Q := (0.611373651876 : ℝ))
      (s := (0.791342061180 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780908682697 : ℝ)) (R := (0.781460730825 : ℝ)) (Q2 := (0.611373651876 : ℝ)) (T := (0.828621476132 : ℝ))
    (B := ((6878281101707479/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249675426923/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (429537997308433/625000000000000) := by
  have hk1 : kappa q ≤ 0.608621918942 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499350853846 : ℝ)) (s := (0.866399864245 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610574136163 : ℝ) ≤ 0.685266723467 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610574136163 : ℝ)) (Q := (0.610574136163 : ℝ))
      (s := (0.791959105162 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780397543126 : ℝ)) (R := (0.780949591254 : ℝ)) (Q2 := (0.610574136163 : ℝ)) (T := (0.828277529077 : ℝ))
    (B := ((429537997308433/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498155290723/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866941110197607/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607824413981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498155290723 : ℝ)) (s := (0.867087830802 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609775161509 : ℝ) ≤ 0.684698139957 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609775161509 : ℝ)) (Q := (0.609775161509 : ℝ))
      (s := (0.792574445972 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779886415035 : ℝ)) (R := (0.780438463163 : ℝ)) (Q2 := (0.609775161509 : ℝ)) (T := (0.827933836134 : ℝ))
    (B := ((6866941110197607/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496959727601/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861280551484367/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607027448865 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496959727601 : ℝ)) (s := (0.867773604775 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608976727325 : ℝ) ≤ 0.684130211869 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608976727325 : ℝ)) (Q := (0.608976727325 : ℝ))
      (s := (0.793188089659 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779375298069 : ℝ)) (R := (0.779927346197 : ℝ)) (Q2 := (0.608976727325 : ℝ)) (T := (0.827590396888 : ℝ))
    (B := ((6861280551484367/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495764164479/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1713906567705467/2500000000000000) := by
  have hk1 : kappa q ≤ 0.606231023001 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495764164479 : ℝ)) (s := (0.868457191357 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608178833016 : ℝ) ≤ 0.683562937995 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608178833016 : ℝ)) (Q := (0.608178833016 : ℝ))
      (s := (0.793800042247 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778864191869 : ℝ)) (R := (0.779416239997 : ℝ)) (Q2 := (0.608178833016 : ℝ)) (T := (0.827247210925 : ℝ))
    (B := ((1713906567705467/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494568601357/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3424989129137177/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605435135804 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494568601357 : ℝ)) (s := (0.869138595710 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607381477998 : ℝ) ≤ 0.682996317135 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607381477998 : ℝ)) (Q := (0.607381477998 : ℝ))
      (s := (0.794410309718 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778353096081 : ℝ)) (R := (0.778905144209 : ℝ)) (Q2 := (0.607381477998 : ℝ)) (T := (0.826904277834 : ℝ))
    (B := ((3424989129137177/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (98674607647/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (855542062992929/1250000000000000) := by
  have hk1 : kappa q ≤ 0.604639786690 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493373038235 : ℝ)) (s := (0.869817822963 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606584661684 : ℝ) ≤ 0.682430348088 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606584661684 : ℝ)) (Q := (0.606584661684 : ℝ))
      (s := (0.795018898021 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777842010350 : ℝ)) (R := (0.778394058478 : ℝ)) (Q2 := (0.606584661684 : ℝ)) (T := (0.826561597202 : ℝ))
    (B := ((855542062992929/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61522184389/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (136774019959357/200000000000000) := by
  have hk1 : kappa q ≤ 0.603844975078 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492177475112 : ℝ)) (s := (0.870494878212 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605788383493 : ℝ) ≤ 0.681865029663 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605788383493 : ℝ)) (Q := (0.605788383493 : ℝ))
      (s := (0.795625813072 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777330934322 : ℝ)) (R := (0.777882982450 : ℝ)) (Q2 := (0.605788383493 : ℝ)) (T := (0.826219168621 : ℝ))
    (B := ((136774019959357/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49098191199/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416535865261639/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603050700393 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490981911990 : ℝ)) (s := (0.871169766521 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604992642846 : ℝ) ≤ 0.681300360668 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604992642846 : ℝ)) (Q := (0.604992642846 : ℝ))
      (s := (0.796231060750 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776819867645 : ℝ)) (R := (0.777371915773 : ℝ)) (Q2 := (0.604992642846 : ℝ)) (T := (0.825876991683 : ℝ))
    (B := ((3416535865261639/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122446587217/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827448691822091/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602256962059 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489786348868 : ℝ)) (s := (0.871842492921 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604197439170 : ℝ) ≤ 0.680736339920 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604197439170 : ℝ)) (Q := (0.604197439170 : ℝ))
      (s := (0.796834646901 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776308809968 : ℝ)) (R := (0.776860858096 : ℝ)) (Q2 := (0.604197439170 : ℝ)) (T := (0.825535065983 : ℝ))
    (B := ((6827448691822091/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244295392873/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364366374422631/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601463759507 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488590785746 : ℝ)) (s := (0.872513062415 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603402771894 : ℝ) ≤ 0.680172966240 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603402771894 : ℝ)) (Q := (0.603402771894 : ℝ))
      (s := (0.797436577335 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775797760942 : ℝ)) (R := (0.776349809070 : ℝ)) (Q2 := (0.603402771894 : ℝ)) (T := (0.825193391119 : ℝ))
    (B := ((1364366374422631/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487395222623/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816221261681609/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600671092166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487395222623 : ℝ)) (s := (0.873181479971 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602608640445 : ℝ) ≤ 0.679610238447 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602608640445 : ℝ)) (Q := (0.602608640445 : ℝ))
      (s := (0.798036857834 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775286720215 : ℝ)) (R := (0.775838768343 : ℝ)) (Q2 := (0.602608640445 : ℝ)) (T := (0.824851966685 : ℝ))
    (B := ((6816221261681609/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486199659501/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (340530842542433/500000000000000) := by
  have hk1 : kappa q ≤ 0.599878959475 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486199659501 : ℝ)) (s := (0.873847750528 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601815044260 : ℝ) ≤ 0.679048155372 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601815044260 : ℝ)) (Q := (0.601815044260 : ℝ))
      (s := (0.798635494142 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774775687441 : ℝ)) (R := (0.775327735569 : ℝ)) (Q2 := (0.601815044260 : ℝ)) (T := (0.824510792283 : ℝ))
    (B := ((340530842542433/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485004096379/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (850627328746421/1250000000000000) := by
  have hk1 : kappa q ≤ 0.599087360870 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485004096379 : ℝ)) (s := (0.874511878991 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601021982777 : ℝ) ≤ 0.678486715846 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601021982777 : ℝ)) (Q := (0.601021982777 : ℝ))
      (s := (0.799232491969 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774264662273 : ℝ)) (R := (0.774816710401 : ℝ)) (Q2 := (0.601021982777 : ℝ)) (T := (0.824169867512 : ℝ))
    (B := ((850627328746421/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483808533257/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399713294721219/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598296295794 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483808533257 : ℝ)) (s := (0.875173870239 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600229455437 : ℝ) ≤ 0.677925918708 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600229455437 : ℝ)) (Q := (0.600229455437 : ℝ))
      (s := (0.799827856996 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773753644366 : ℝ)) (R := (0.774305692494 : ℝ)) (Q2 := (0.600229455437 : ℝ)) (T := (0.823829191979 : ℝ))
    (B := ((3399713294721219/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96522594027/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1358768143938003/2000000000000000) := by
  have hk1 : kappa q ≤ 0.597505763691 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482612970135 : ℝ)) (s := (0.875833729117 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599437461679 : ℝ) ≤ 0.677365762794 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599437461679 : ℝ)) (Q := (0.599437461679 : ℝ))
      (s := (0.800421594872 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773242633373 : ℝ)) (R := (0.773794681501 : ℝ)) (Q2 := (0.599437461679 : ℝ)) (T := (0.823488765284 : ℝ))
    (B := ((1358768143938003/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120354351753/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (169706525279437/250000000000000) := by
  have hk1 : kappa q ≤ 0.596715764008 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481417407012 : ℝ)) (s := (0.876491460441 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598646000955 : ℝ) ≤ 0.676806246953 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598646000955 : ℝ)) (Q := (0.598646000955 : ℝ))
      (s := (0.801013711207 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772731628952 : ℝ)) (R := (0.773283677080 : ℝ)) (Q2 := (0.598646000955 : ℝ)) (T := (0.823148587037 : ℝ))
    (B := ((169706525279437/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48022184389/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782686403860129/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595926296197 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480221843890 : ℝ)) (s := (0.877147068998 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597855072713 : ℝ) ≤ 0.676247370034 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597855072713 : ℝ)) (Q := (0.597855072713 : ℝ))
      (s := (0.801604211586 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772220630761 : ℝ)) (R := (0.772772678889 : ℝ)) (Q2 := (0.597855072713 : ℝ)) (T := (0.822808656844 : ℝ))
    (B := ((6782686403860129/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (7484785637/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777117790140733/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595137359712 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479026280768 : ℝ)) (s := (0.877800559543 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597064676406 : ℝ) ≤ 0.675689130889 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597064676406 : ℝ)) (Q := (0.597064676406 : ℝ))
      (s := (0.802193101559 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771709638457 : ℝ)) (R := (0.772261686585 : ℝ)) (Q2 := (0.597064676406 : ℝ)) (T := (0.822468974316 : ℝ))
    (B := ((6777117790140733/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12550 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (238915358823/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1354311062379019/2000000000000000) := by
  have hk1 : kappa q ≤ 0.594348954009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477830717646 : ℝ)) (s := (0.878451936804 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596274811488 : ℝ) ≤ 0.675131528376 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596274811488 : ℝ)) (Q := (0.596274811488 : ℝ))
      (s := (0.802780386647 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771198651700 : ℝ)) (R := (0.771750699828 : ℝ)) (Q2 := (0.596274811488 : ℝ)) (T := (0.822129539064 : ℝ))
    (B := ((1354311062379019/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S8
namespace BstLean.Part269.S8
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12550 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052800443592 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S8.wn_upper (by omega : 12550 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010660286356 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036024472514)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010660286356 + 2 * 0.737676 / 12550) := by gcongr
    _ ≤ (0.052800443592 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12550 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12550 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.026782512040 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12550 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.026782512040 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12550 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003697790472 + 0.003334422039 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003697790472 + 0.003334422039 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.026782512040 ≤ R)
    (hB : (X + 0.052800443592 + R + 0.008532178410) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008532178410 := by
    convert (BstLean.Part269.S8.finite_centre_upper (by omega : 12550 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (1341667111/15625000000)
  | 2 => (2170414213/25000000000)
  | 3 => (10970706757/125000000000)
  | 4 => (88715614367/1000000000000)
  | 5 => (89668452021/1000000000000)
  | 6 => (5664159929/62500000000)
  | 7 => (91592769833/1000000000000)
  | 8 => (23142605303/250000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003697790472 + 0.003334422039 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219537477568 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011031893007 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003697790472 + 0.003334422039 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.221105617864 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011147545307 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003697790472 + 0.003334422039 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222653330188 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011262815616 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003697790472 + 0.003334422039 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224180820696 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011377712309 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003697790472 + 0.003334422039 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225688290429 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011492243520 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003697790472 + 0.003334422039 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227175933819 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011606417031 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003697790472 + 0.003334422039 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228643940564 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011720240414 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12550 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003697790472 + 0.003334422039 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.230092494156 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011833720914 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12550 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g) :
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

end BstLean.Part269.S8

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S18
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12800 ≤ n) : wn n ≤ 1.035667839060 := by
  have hnR : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.137084989847 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.137084989847 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035667839060 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12800 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12800 + 24 / (12800 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12800 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008448086818 : ℝ) := by
  have hnR : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.137084989847 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12800 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035667839060 * (81 / 1000 / 12800)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035667839060 * n *
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
        4 * (1 / 2.506628) * 1.035667839060 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035667839060 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035667839060 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12800)) / 113.137084989847 := by gcongr
    _ ≤ (0.008448086818 : ℝ) := by norm_num

end BstLean.Part269.S18
namespace BstLean.Part269.S18
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12800 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12800 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12800 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12800 + 0.008448086818 / 113.137084989847) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12800 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12800 := by gcongr
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
  have hn : (113.137084989847 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S18.finite_centre_upper (by omega : 12800 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264035564971/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3505012469814797/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627943730605 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528071129942 : ℝ)) (s := (0.849200142324 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629906523586 : ℝ) ≤ 0.699107715122 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629906523586 : ℝ)) (Q := (0.629906523586 : ℝ))
      (s := (0.776670954488 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792675441531 : ℝ)) (R := (0.793216707469 : ℝ)) (Q2 := (0.629906523586 : ℝ)) (T := (0.836600471831 : ℝ))
    (B := ((3505012469814797/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65859780367/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004217502558633/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627134885877 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526878242936 : ℝ)) (s := (0.849940772714 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629096208163 : ℝ) ≤ 0.698524337884 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629096208163 : ℝ)) (Q := (0.629096208163 : ℝ))
      (s := (0.777327447654 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792165078047 : ℝ)) (R := (0.792706343985 : ℝ)) (Q2 := (0.629096208163 : ℝ)) (T := (0.836251344279 : ℝ))
    (B := ((7004217502558633/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525685355931/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998416575126143/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626326593619 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525685355931 : ℝ)) (s := (0.850679085531 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628286445860 : ℝ) ≤ 0.697941643233 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628286445860 : ℝ)) (Q := (0.628286445860 : ℝ))
      (s := (0.777982096162 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791654734477 : ℝ)) (R := (0.792196000415 : ℝ)) (Q2 := (0.628286445860 : ℝ)) (T := (0.835902479665 : ℝ))
    (B := ((6998416575126143/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20979698757/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6992622146458587/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625518853168 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524492468925 : ℝ)) (s := (0.851415086807 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477236011 : ℝ) ≤ 0.697359629870 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477236011 : ℝ)) (Q := (0.627477236011 : ℝ))
      (s := (0.778634906929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791144410439 : ℝ)) (R := (0.791685676377 : ℝ)) (Q2 := (0.627477236011 : ℝ)) (T := (0.835553877540 : ℝ))
    (B := ((6992622146458587/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523299581919/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986834205725587/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624711663869 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523299581919 : ℝ)) (s := (0.852148782528 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668577960 : ℝ) ≤ 0.696778296501 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668577960 : ℝ)) (Q := (0.626668577960 : ℝ))
      (s := (0.779285886821 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790634105557 : ℝ)) (R := (0.791175371495 : ℝ)) (Q2 := (0.626668577960 : ℝ)) (T := (0.835205537457 : ℝ))
    (B := ((6986834205725587/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522106694913/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27269737273983/39062500000000) := by
  have hk1 : kappa q ≤ 0.623905025068 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522106694913 : ℝ)) (s := (0.852880178646 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625860471051 : ℝ) ≤ 0.696197641836 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625860471051 : ℝ)) (Q := (0.625860471051 : ℝ))
      (s := (0.779935042665 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790123819454 : ℝ)) (R := (0.790665085392 : ℝ)) (Q2 := (0.625860471051 : ℝ)) (T := (0.834857458971 : ℝ))
    (B := ((27269737273983/39062500000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520913807907/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1395055548991179/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623098936112 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520913807907 : ℝ)) (s := (0.853609281072 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625052914633 : ℝ) ≤ 0.695617664590 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625052914633 : ℝ)) (Q := (0.625052914633 : ℝ))
      (s := (0.780582381245 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789613551754 : ℝ)) (R := (0.790154817692 : ℝ)) (Q2 := (0.625052914633 : ℝ)) (T := (0.834509641638 : ℝ))
    (B := ((1395055548991179/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259860460451/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1393901840694361/2000000000000000) := by
  have hk1 : kappa q ≤ 0.622293396357 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519720920902 : ℝ)) (s := (0.854336095678 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624245908056 : ℝ) ≤ 0.695038363481 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624245908056 : ℝ)) (Q := (0.624245908056 : ℝ))
      (s := (0.781227909304 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789103302083 : ℝ)) (R := (0.789644568021 : ℝ)) (Q2 := (0.624245908056 : ℝ)) (T := (0.834162085016 : ℝ))
    (B := ((1393901840694361/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64816004237/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (348187355351347/500000000000000) := by
  have hk1 : kappa q ≤ 0.621488405153 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518528033896 : ℝ)) (s := (0.855060628298 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623439450673 : ℝ) ≤ 0.694459737230 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623439450673 : ℝ)) (Q := (0.623439450673 : ℝ))
      (s := (0.781871633547 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788593070065 : ℝ)) (R := (0.789134336003 : ℝ)) (Q2 := (0.623439450673 : ℝ)) (T := (0.833814788662 : ℝ))
    (B := ((348187355351347/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51733514689/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3478995722501343/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620683961862 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517335146890 : ℝ)) (s := (0.855782884728 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622633541843 : ℝ) ≤ 0.693881784565 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622633541843 : ℝ)) (Q := (0.622633541843 : ℝ))
      (s := (0.782513560632 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788082855329 : ℝ)) (R := (0.788624121267 : ℝ)) (Q2 := (0.622633541843 : ℝ)) (T := (0.833467752139 : ℝ))
    (B := ((3478995722501343/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129035564971/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952242206821999/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619880065844 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516142259884 : ℝ)) (s := (0.856502870726 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621828180924 : ℝ) ≤ 0.693304504214 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621828180924 : ℝ)) (Q := (0.621828180924 : ℝ))
      (s := (0.783153697182 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787572657502 : ℝ)) (R := (0.788113923440 : ℝ)) (Q2 := (0.621828180924 : ℝ)) (T := (0.833120975006 : ℝ))
    (B := ((6952242206821999/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257474686439/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473249690974569/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619076716463 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514949372878 : ℝ)) (s := (0.857220592014 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621023367281 : ℝ) ≤ 0.692727894913 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621023367281 : ℝ)) (Q := (0.621023367281 : ℝ))
      (s := (0.783792049776 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787062476214 : ℝ)) (R := (0.787603742152 : ℝ)) (Q2 := (0.621023367281 : ℝ)) (T := (0.832774456829 : ℝ))
    (B := ((3473249690974569/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32109780367/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (347038147994471/500000000000000) := by
  have hk1 : kappa q ≤ 0.618273913087 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513756485872 : ℝ)) (s := (0.857936054275 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620219100279 : ℝ) ≤ 0.692151955400 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620219100279 : ℝ)) (Q := (0.620219100279 : ℝ))
      (s := (0.784428624956 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786552311094 : ℝ)) (R := (0.787093577032 : ℝ)) (Q2 := (0.620219100279 : ℝ)) (T := (0.832428197171 : ℝ))
    (B := ((347038147994471/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512563598867/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (43343955813681/62500000000000) := by
  have hk1 : kappa q ≤ 0.617471655087 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512563598867 : ℝ)) (s := (0.858649263155 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619415379290 : ℝ) ≤ 0.691576684420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619415379290 : ℝ)) (Q := (0.619415379290 : ℝ))
      (s := (0.785063429221 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786042161775 : ℝ)) (R := (0.786583427713 : ℝ)) (Q2 := (0.619415379290 : ℝ)) (T := (0.832082195600 : ℝ))
    (B := ((43343955813681/62500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511370711861/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3464654641217211/5000000000000000) := by
  have hk1 : kappa q ≤ 0.616669941835 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511370711861 : ℝ)) (s := (0.859360224267 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618612203684 : ℝ) ≤ 0.691002080716 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618612203684 : ℝ)) (Q := (0.618612203684 : ℝ))
      (s := (0.785696469035 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785532027887 : ℝ)) (R := (0.786073293825 : ℝ)) (Q2 := (0.618612203684 : ℝ)) (T := (0.831736451682 : ℝ))
    (B := ((3464654641217211/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102035564971/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (276943680250111/400000000000000) := by
  have hk1 : kappa q ≤ 0.615868772710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510177824855 : ℝ)) (s := (0.860068943183 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617809572837 : ℝ) ≤ 0.690428143040 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617809572837 : ℝ)) (Q := (0.617809572837 : ℝ))
      (s := (0.786327750821 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785021909064 : ℝ)) (R := (0.785563175002 : ℝ)) (Q2 := (0.617809572837 : ℝ)) (T := (0.831390964986 : ℝ))
    (B := ((276943680250111/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508984937849/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (21618378410347/31250000000000) := by
  have hk1 : kappa q ≤ 0.615068147089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508984937849 : ℝ)) (s := (0.860775425441 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617007486128 : ℝ) ≤ 0.689854870148 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617007486128 : ℝ)) (Q := (0.617007486128 : ℝ))
      (s := (0.786957280964 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784511804940 : ℝ)) (R := (0.785053070878 : ℝ)) (Q2 := (0.617007486128 : ℝ)) (T := (0.831045735085 : ℝ))
    (B := ((21618378410347/31250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507792050843/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912176527316051/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614268064357 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507792050843 : ℝ)) (s := (0.861479676546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616205942939 : ℝ) ≤ 0.689282260799 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616205942939 : ℝ)) (Q := (0.616205942939 : ℝ))
      (s := (0.787585065810 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784001715150 : ℝ)) (R := (0.784542981088 : ℝ)) (Q2 := (0.616205942939 : ℝ)) (T := (0.830700761551 : ℝ))
    (B := ((6912176527316051/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253299581919/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906478304014211/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613468523900 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506599163838 : ℝ)) (s := (0.862181701963 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615404942654 : ℝ) ≤ 0.688710313755 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615404942654 : ℝ)) (Q := (0.615404942654 : ℝ))
      (s := (0.788211111669 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783491639330 : ℝ)) (R := (0.784032905268 : ℝ)) (Q2 := (0.615404942654 : ℝ)) (T := (0.830356043957 : ℝ))
    (B := ((6906478304014211/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15793946151/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1725196602797813/2500000000000000) := by
  have hk1 : kappa q ≤ 0.612669525106 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505406276832 : ℝ)) (s := (0.862881507126 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614604484663 : ℝ) ≤ 0.688139027785 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614604484663 : ℝ)) (Q := (0.614604484663 : ℝ))
      (s := (0.788835424809 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782981577118 : ℝ)) (R := (0.783522843056 : ℝ)) (Q2 := (0.614604484663 : ℝ)) (T := (0.830011581879 : ℝ))
    (B := ((1725196602797813/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252106694913/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447550419335999/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611871067368 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504213389826 : ℝ)) (s := (0.863579097432 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613804568356 : ℝ) ≤ 0.687568401661 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613804568356 : ℝ)) (Q := (0.613804568356 : ℝ))
      (s := (0.789458011465 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782471528152 : ℝ)) (R := (0.783012794090 : ℝ)) (Q2 := (0.613804568356 : ℝ)) (T := (0.829667374894 : ℝ))
    (B := ((3447550419335999/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25151025141/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444710788160063/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611073150081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503020502820 : ℝ)) (s := (0.864274478244 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613005193127 : ℝ) ≤ 0.686998434156 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613005193127 : ℝ)) (Q := (0.613005193127 : ℝ))
      (s := (0.790078877834 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781961492071 : ℝ)) (R := (0.782502758009 : ℝ)) (Q2 := (0.613005193127 : ℝ)) (T := (0.829323422581 : ℝ))
    (B := ((3444710788160063/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250913807907/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883748614037939/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610275772644 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501827615814 : ℝ)) (s := (0.864967654891 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612206358373 : ℝ) ≤ 0.686429124054 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612206358373 : ℝ)) (Q := (0.612206358373 : ℝ))
      (s := (0.790698030078 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781451468515 : ℝ)) (R := (0.781992734453 : ℝ)) (Q2 := (0.612206358373 : ℝ)) (T := (0.828979724521 : ℝ))
    (B := ((6883748614037939/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62579341101/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439040970883063/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609478934458 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500634728808 : ℝ)) (s := (0.865658632668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611408063495 : ℝ) ≤ 0.685860470135 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611408063495 : ℝ)) (Q := (0.611408063495 : ℝ))
      (s := (0.791315474317 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780941457126 : ℝ)) (R := (0.781482723064 : ℝ)) (Q2 := (0.611408063495 : ℝ)) (T := (0.828636280294 : ℝ))
    (B := ((3439040970883063/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499441841803/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3436210774741769/5000000000000000) := by
  have hk1 : kappa q ≤ 0.608682634929 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499441841803 : ℝ)) (s := (0.866347416835 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610610307900 : ℝ) ≤ 0.685292471194 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610610307900 : ℝ)) (Q := (0.610610307900 : ℝ))
      (s := (0.791931216639 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780431457548 : ℝ)) (R := (0.780972723486 : ℝ)) (Q2 := (0.610610307900 : ℝ)) (T := (0.828293089488 : ℝ))
    (B := ((3436210774741769/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498248954797/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866767427206957/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607886873464 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498248954797 : ℝ)) (s := (0.867034012623 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609813090990 : ℝ) ≤ 0.684725126018 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609813090990 : ℝ)) (Q := (0.609813090990 : ℝ))
      (s := (0.792545263097 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779921469422 : ℝ)) (R := (0.780462735360 : ℝ)) (Q2 := (0.609813090990 : ℝ)) (T := (0.827950151683 : ℝ))
    (B := ((6866767427206957/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497056067791/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861119564990873/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607091649472 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497056067791 : ℝ)) (s := (0.867718425224 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609016412175 : ℝ) ≤ 0.684158433405 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609016412175 : ℝ)) (Q := (0.609016412175 : ℝ))
      (s := (0.793157619709 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779411492392 : ℝ)) (R := (0.779952758330 : ℝ)) (Q2 := (0.609016412175 : ℝ)) (T := (0.827607466469 : ℝ))
    (B := ((6861119564990873/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99172636157/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (856934744115907/1250000000000000) := by
  have hk1 : kappa q ≤ 0.606296962370 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495863180785 : ℝ)) (s := (0.868400659801 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608220270870 : ℝ) ≤ 0.683592392158 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608220270870 : ℝ)) (Q := (0.608220270870 : ℝ))
      (s := (0.793768292453 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778901526106 : ℝ)) (R := (0.779442792044 : ℝ)) (Q2 := (0.608220270870 : ℝ)) (T := (0.827265033433 : ℝ))
    (B := ((856934744115907/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494670293779/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849842581145337/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605502811574 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494670293779 : ℝ)) (s := (0.869080721483 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607424666492 : ℝ) ≤ 0.683027001083 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607424666492 : ℝ)) (Q := (0.607424666492 : ℝ))
      (s := (0.794377287275 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778391570211 : ℝ)) (R := (0.778932836149 : ℝ)) (Q2 := (0.607424666492 : ℝ)) (T := (0.826922852168 : ℝ))
    (B := ((6849842581145337/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493477406773/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422106719905693/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604709196504 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493477406773 : ℝ)) (s := (0.869758615367 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606629598457 : ℝ) ≤ 0.682462258987 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606629598457 : ℝ)) (Q := (0.606629598457 : ℝ))
      (s := (0.794984610088 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777881624352 : ℝ)) (R := (0.778422890290 : ℝ)) (Q2 := (0.606629598457 : ℝ)) (T := (0.826580922262 : ℝ))
    (B := ((3422106719905693/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61535564971/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419295259564247/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603916116584 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492284519768 : ℝ)) (s := (0.870434346518 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605835066192 : ℝ) ≤ 0.681898164687 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605835066192 : ℝ)) (Q := (0.605835066192 : ℝ))
      (s := (0.795590266766 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777371688181 : ℝ)) (R := (0.777912954119 : ℝ)) (Q2 := (0.605835066192 : ℝ)) (T := (0.826239243312 : ℝ))
    (B := ((3419295259564247/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245545816381/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1708243452334089/2500000000000000) := by
  have hk1 : kappa q ≤ 0.603123571240 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491091632762 : ℝ)) (s := (0.871107919969 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605041069117 : ℝ) ≤ 0.681334716999 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605041069117 : ℝ)) (Q := (0.605041069117 : ℝ))
      (s := (0.796194263156 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776861761345 : ℝ)) (R := (0.777403027283 : ℝ)) (Q2 := (0.605041069117 : ℝ)) (T := (0.825897814911 : ℝ))
    (B := ((1708243452334089/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122474686439/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827363300711059/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602331559901 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489898745756 : ℝ)) (s := (0.871779340721 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604247606664 : ℝ) ≤ 0.680771914747 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604247606664 : ℝ)) (Q := (0.604247606664 : ℝ))
      (s := (0.796796605064 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776351843497 : ℝ)) (R := (0.776893109435 : ℝ)) (Q2 := (0.604247606664 : ℝ)) (T := (0.825556636658 : ℝ))
    (B := ((6827363300711059/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (390964687/800000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821758983564863/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601540082001 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488705858750 : ℝ)) (s := (0.872448613744 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603454678264 : ℝ) ≤ 0.680209756758 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603454678264 : ℝ)) (Q := (0.603454678264 : ℝ))
      (s := (0.797397298266 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775841934289 : ℝ)) (R := (0.776383200227 : ℝ)) (Q2 := (0.603454678264 : ℝ)) (T := (0.825215708150 : ℝ))
    (B := ((6821758983564863/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15234780367/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1363232169649199/2000000000000000) := by
  have hk1 : kappa q ≤ 0.600749136974 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487512971744 : ℝ)) (s := (0.873115743978 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602662283351 : ℝ) ≤ 0.679648241862 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602662283351 : ℝ)) (Q := (0.602662283351 : ℝ))
      (s := (0.797996348505 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775332033373 : ℝ)) (R := (0.775873299311 : ℝ)) (Q2 := (0.602662283351 : ℝ)) (T := (0.824875028987 : ℝ))
    (B := ((1363232169649199/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486320084739/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405284442569219/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599958724261 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486320084739 : ℝ)) (s := (0.873780736329 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601870421364 : ℝ) ≤ 0.679087368895 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601870421364 : ℝ)) (Q := (0.601870421364 : ℝ))
      (s := (0.798593761488 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774822140405 : ℝ)) (R := (0.775363406343 : ℝ)) (Q2 := (0.601870421364 : ℝ)) (T := (0.824534598773 : ℝ))
    (B := ((3405284442569219/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485127197733/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804983084661723/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599168843302 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485127197733 : ℝ)) (s := (0.874443595677 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601079091742 : ℝ) ≤ 0.678527136696 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601079091742 : ℝ)) (Q := (0.601079091742 : ℝ))
      (s := (0.799189542894 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774312255038 : ℝ)) (R := (0.774853520976 : ℝ)) (Q2 := (0.601079091742 : ℝ)) (T := (0.824194417109 : ℝ))
    (B := ((6804983084661723/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483934310727/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799403437270721/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598379493543 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483934310727 : ℝ)) (s := (0.875104326867 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600288293932 : ℝ) ≤ 0.677967544110 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600288293932 : ℝ)) (Q := (0.600288293932 : ℝ))
      (s := (0.799783698364 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773802376931 : ℝ)) (R := (0.774343642869 : ℝ)) (Q2 := (0.600288293932 : ℝ)) (T := (0.823854483603 : ℝ))
    (B := ((6799403437270721/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482741423721/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793829933455443/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597590674432 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482741423721 : ℝ)) (s := (0.875762934717 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599498027378 : ℝ) ≤ 0.677408589984 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599498027378 : ℝ)) (Q := (0.599498027378 : ℝ))
      (s := (0.800376233512 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773292505739 : ℝ)) (R := (0.773833771677 : ℝ)) (Q2 := (0.599498027378 : ℝ)) (T := (0.823514797861 : ℝ))
    (B := ((6793829933455443/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96309707343/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788262174195143/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596802385419 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481548536715 : ℝ)) (s := (0.876419424014 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598708291532 : ℝ) ≤ 0.676850273172 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598708291532 : ℝ)) (Q := (0.598708291532 : ℝ))
      (s := (0.800967153916 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772782641122 : ℝ)) (R := (0.773323907060 : ℝ)) (Q2 := (0.598708291532 : ℝ)) (T := (0.823175359492 : ℝ))
    (B := ((6788262174195143/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480355649709/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3391349881690437/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596014625959 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480355649709 : ℝ)) (s := (0.877073799514 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597919085845 : ℝ) ≤ 0.676292592528 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597919085845 : ℝ)) (Q := (0.597919085845 : ℝ))
      (s := (0.801556465125 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772272782739 : ℝ)) (R := (0.772814048677 : ℝ)) (Q2 := (0.597919085845 : ℝ)) (T := (0.822836168107 : ℝ))
    (B := ((3391349881690437/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (29947672669/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777143470376989/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595227395510 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479162762704 : ℝ)) (s := (0.877726065945 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597130409777 : ℝ) ≤ 0.675735546915 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597130409777 : ℝ)) (Q := (0.597130409777 : ℝ))
      (s := (0.802144172652 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771762930252 : ℝ)) (R := (0.772304196190 : ℝ)) (Q2 := (0.597130409777 : ℝ)) (T := (0.822497223317 : ℝ))
    (B := ((6777143470376989/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12800 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (238984937849/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771593285806303/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594440693531 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477969875698 : ℝ)) (s := (0.878376228006 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596342262784 : ℝ) ≤ 0.675179135198 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596342262784 : ℝ)) (Q := (0.596342262784 : ℝ))
      (s := (0.802730281987 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771253083321 : ℝ)) (R := (0.771794349259 : ℝ)) (Q2 := (0.596342262784 : ℝ)) (T := (0.822158524738 : ℝ))
    (B := ((6771593285806303/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S18
namespace BstLean.Part269.S18
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12800 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052276675219 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S18.wn_upper (by omega : 12800 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010555668649 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035667839060)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010555668649 + 2 * 0.737676 / 12800) := by gcongr
    _ ≤ (0.052276675219 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12800 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12800 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.137084989847 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12800 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.137084989847 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12800 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003402164259 + 0.003267039105 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003402164259 + 0.003267039105 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.137084989847 ≤ R)
    (hB : (X + 0.052276675219 + R + 0.008448086818) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008448086818 := by
    convert (BstLean.Part269.S18.finite_centre_upper (by omega : 12800 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (85136633657/1000000000000)
  | 2 => (86073063623/1000000000000)
  | 3 => (43503370151/500000000000)
  | 4 => (21984718519/250000000000)
  | 5 => (88870935489/1000000000000)
  | 6 => (280639671/3125000000)
  | 7 => (45371132461/500000000000)
  | 8 => (91686149511/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003402164259 + 0.003267039105 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218790109086 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010923628435 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003402164259 + 0.003267039105 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220362467535 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011038145748 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003402164259 + 0.003267039105 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221914270296 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011152284819 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003402164259 + 0.003267039105 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223445727986 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011266053941 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003402164259 + 0.003267039105 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224957045886 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011379461169 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003402164259 + 0.003267039105 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226448422459 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011492514206 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003402164259 + 0.003267039105 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227920051232 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011605220551 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12800 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003402164259 + 0.003267039105 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229372119348 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011717587379 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12800 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g) :
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

end BstLean.Part269.S18

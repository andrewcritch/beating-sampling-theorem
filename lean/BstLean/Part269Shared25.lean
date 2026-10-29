import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S25
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12975 ≤ n) : wn n ≤ 1.035424387669 := by
  have hnR : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.907857498945 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.907857498945 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035424387669 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12975 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12975 + 24 / (12975 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12975 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008390678547 : ℝ) := by
  have hnR : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.907857498945 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12975 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035424387669 * (81 / 1000 / 12975)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035424387669 * n *
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
        4 * (1 / 2.506628) * 1.035424387669 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035424387669 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035424387669 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12975)) / 113.907857498945 := by gcongr
    _ ≤ (0.008390678547 : ℝ) := by norm_num

end BstLean.Part269.S25
namespace BstLean.Part269.S25
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12975 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12975 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12975 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12975 + 0.008390678547 / 113.907857498945) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12975 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12975 := by gcongr
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
  have hn : (113.907857498945 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S25.finite_centre_upper (by omega : 12975 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528086500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7009672765611629/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627954155981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528086500001 : ℝ)) (s := (0.849190584332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629900095202 : ℝ) ≤ 0.699103085960 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629900095202 : ℝ)) (Q := (0.629900095202 : ℝ))
      (s := (0.776676168081 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792678694325 : ℝ)) (R := (0.793212659952 : ℝ)) (Q2 := (0.629900095202 : ℝ)) (T := (0.836597702039 : ℝ))
    (B := ((7009672765611629/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526895150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3501936544302133/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627146345960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526895150001 : ℝ)) (s := (0.849930291792 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629090823821 : ℝ) ≤ 0.698520462441 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629090823821 : ℝ)) (Q := (0.629090823821 : ℝ))
      (s := (0.777331805206 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792168986022 : ℝ)) (R := (0.792702951649 : ℝ)) (Q2 := (0.629090823821 : ℝ)) (T := (0.836249024497 : ℝ))
    (B := ((3501936544302133/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525703800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (437379994011127/625000000000000) := by
  have hk1 : kappa q ≤ 0.626339086996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525703800001 : ℝ)) (s := (0.850667687564 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628282104144 : ℝ) ≤ 0.697938519756 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628282104144 : ℝ)) (Q := (0.628282104144 : ℝ))
      (s := (0.777985602446 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791659297584 : ℝ)) (R := (0.792193263211 : ℝ)) (Q2 := (0.628282104144 : ℝ)) (T := (0.835900609218 : ℝ))
    (B := ((437379994011127/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524512450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6992293201501847/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625532378429 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524512450001 : ℝ)) (s := (0.851402777653 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627473935509 : ℝ) ≤ 0.697357256609 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627473935509 : ℝ)) (Q := (0.627473935509 : ℝ))
      (s := (0.778637566688 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791149628632 : ℝ)) (R := (0.791683594259 : ℝ)) (Q2 := (0.627473935509 : ℝ)) (T := (0.835552455756 : ℝ))
    (B := ((6992293201501847/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523321100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1746628242446891/2500000000000000) := by
  have hk1 : kappa q ≤ 0.624726219604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523321100001 : ℝ)) (s := (0.852135568026 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626666317261 : ℝ) ≤ 0.696776671711 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626666317261 : ℝ)) (Q := (0.626666317261 : ℝ))
      (s := (0.779287704774 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790639978789 : ℝ)) (R := (0.791173944416 : ℝ)) (Q2 := (0.626666317261 : ℝ)) (T := (0.835204563665 : ℝ))
    (B := ((1746628242446891/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522129750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6980739198289701/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623920609872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522129750001 : ℝ)) (s := (0.852866064611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859248749 : ℝ) ≤ 0.696196763781 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859248749 : ℝ)) (Q := (0.625859248749 : ℝ))
      (s := (0.779936023502 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790130347682 : ℝ)) (R := (0.790664313309 : ℝ)) (Q2 := (0.625859248749 : ℝ)) (T := (0.834856932503 : ℝ))
    (B := ((6980739198289701/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520938400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (278998875052207/400000000000000) := by
  have hk1 : kappa q ≤ 0.623115548582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520938400001 : ℝ)) (s := (0.853594273297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625052729319 : ℝ) ≤ 0.695617531532 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625052729319 : ℝ)) (Q := (0.625052729319 : ℝ))
      (s := (0.780582529635 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789620734934 : ℝ)) (R := (0.790154700561 : ℝ)) (Q2 := (0.625052729319 : ℝ)) (T := (0.834509561825 : ℝ))
    (B := ((278998875052207/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519747050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (871151374146629/1250000000000000) := by
  have hk1 : kappa q ≤ 0.622311035089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519747050001 : ℝ)) (s := (0.854320199934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624246758329 : ℝ) ≤ 0.695038973693 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624246758329 : ℝ)) (Q := (0.624246758329 : ℝ))
      (s := (0.781227229887 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789111140173 : ℝ)) (R := (0.789645105800 : ℝ)) (Q2 := (0.624246758329 : ℝ)) (T := (0.834162451194 : ℝ))
    (B := ((871151374146629/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518555700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6963456538274191/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621507068752 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518555700001 : ℝ)) (s := (0.855043850336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623441335132 : ℝ) ≤ 0.694461088986 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623441335132 : ℝ)) (Q := (0.623441335132 : ℝ))
      (s := (0.781870130936 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788601563026 : ℝ)) (R := (0.789135528653 : ℝ)) (Q2 := (0.623441335132 : ℝ)) (T := (0.833815600166 : ℝ))
    (B := ((6963456538274191/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517364350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6957708501031181/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620703648931 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517364350001 : ℝ)) (s := (0.855765230276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622636459091 : ℝ) ≤ 0.693883876147 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622636459091 : ℝ)) (Q := (0.622636459091 : ℝ))
      (s := (0.782511239415 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788092003123 : ℝ)) (R := (0.788625968750 : ℝ)) (Q2 := (0.622636459091 : ℝ)) (T := (0.833469008307 : ℝ))
    (B := ((6957708501031181/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516173000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (173799171772697/250000000000000) := by
  have hk1 : kappa q ≤ 0.619900774988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516173000001 : ℝ)) (s := (0.856484345491 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621832129565 : ℝ) ≤ 0.693307333907 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621832129565 : ℝ)) (Q := (0.621832129565 : ℝ))
      (s := (0.783150561924 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787582460091 : ℝ)) (R := (0.788116425718 : ℝ)) (Q2 := (0.621832129565 : ℝ)) (T := (0.833122675179 : ℝ))
    (B := ((173799171772697/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514981650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389246327481853/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619098446292 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514981650001 : ℝ)) (s := (0.857201201681 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621028345922 : ℝ) ≤ 0.692731461008 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621028345922 : ℝ)) (Q := (0.621028345922 : ℝ))
      (s := (0.783788105014 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787072933563 : ℝ)) (R := (0.787606899190 : ℝ)) (Q2 := (0.621028345922 : ℝ)) (T := (0.832776600347 : ℝ))
    (B := ((1389246327481853/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513790300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1735125697520289/2500000000000000) := by
  have hk1 : kappa q ≤ 0.618296662211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513790300001 : ℝ)) (s := (0.857915804509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620225107529 : ℝ) ≤ 0.692156256191 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620225107529 : ℝ)) (Q := (0.620225107529 : ℝ))
      (s := (0.784423875205 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786563423168 : ℝ)) (R := (0.787097388795 : ℝ)) (Q2 := (0.620225107529 : ℝ)) (T := (0.832430783376 : ℝ))
    (B := ((1735125697520289/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512598950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1733695079627491/2500000000000000) := by
  have hk1 : kappa q ≤ 0.617495422118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512598950001 : ℝ)) (s := (0.858628159600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619422413759 : ℝ) ≤ 0.691581718205 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619422413759 : ℝ)) (Q := (0.619422413759 : ℝ))
      (s := (0.785057878971 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786053928540 : ℝ)) (R := (0.786587894167 : ℝ)) (Q2 := (0.619422413759 : ℝ)) (T := (0.832085223836 : ℝ))
    (B := ((1733695079627491/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511407600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929064212322443/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616694725391 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511407600001 : ℝ)) (s := (0.859338272546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618620263987 : ℝ) ≤ 0.691007845802 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618620263987 : ℝ)) (Q := (0.618620263987 : ℝ))
      (s := (0.785690122749 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785544449313 : ℝ)) (R := (0.786078414940 : ℝ)) (Q2 := (0.618620263987 : ℝ)) (T := (0.831739921296 : ℝ))
    (B := ((6929064212322443/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510216250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923354461185443/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615894571407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510216250001 : ℝ)) (s := (0.860046148899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617818657590 : ℝ) ≤ 0.690434637735 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617818657590 : ℝ)) (Q := (0.617818657590 : ℝ))
      (s := (0.786320612940 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785034985120 : ℝ)) (R := (0.785568950747 : ℝ)) (Q2 := (0.617818657590 : ℝ)) (T := (0.831394875327 : ℝ))
    (B := ((6923354461185443/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509024900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1383530210961133/2000000000000000) := by
  have hk1 : kappa q ≤ 0.615094959549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509024900001 : ℝ)) (s := (0.860751794178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617017593949 : ℝ) ≤ 0.689862092766 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617017593949 : ℝ)) (Q := (0.617017593949 : ℝ))
      (s := (0.786949355904 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784525535597 : ℝ)) (R := (0.785059501224 : ℝ)) (Q2 := (0.617017593949 : ℝ)) (T := (0.831050085500 : ℝ))
    (B := ((1383530210961133/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507833550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6911953982929421/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614295889201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507833550001 : ℝ)) (s := (0.861455213864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616217072449 : ℝ) ≤ 0.689290209658 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616217072449 : ℝ)) (Q := (0.616217072449 : ℝ))
      (s := (0.787576357964 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784016100381 : ℝ)) (R := (0.784550066008 : ℝ)) (Q2 := (0.616217072449 : ℝ)) (T := (0.830705551392 : ℝ))
    (B := ((6911953982929421/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506642200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1726565808835597/2500000000000000) := by
  have hk1 : kappa q ≤ 0.613497359753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506642200001 : ℝ)) (s := (0.862156413407 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615417092477 : ℝ) ≤ 0.688718987179 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615417092477 : ℝ)) (Q := (0.615417092477 : ℝ))
      (s := (0.788201625403 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783506679109 : ℝ)) (R := (0.784040644736 : ℝ)) (Q2 := (0.615417092477 : ℝ)) (T := (0.830361272575 : ℝ))
    (B := ((1726565808835597/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505450850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (107821543779209/156250000000000) := by
  have hk1 : kappa q ≤ 0.612699370595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505450850001 : ℝ)) (s := (0.862855398218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614617653423 : ℝ) ≤ 0.688148424101 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614617653423 : ℝ)) (Q := (0.614617653423 : ℝ))
      (s := (0.788825164470 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782997271420 : ℝ)) (R := (0.783531237047 : ℝ)) (Q2 := (0.614617653423 : ℝ)) (T := (0.830017248629 : ℝ))
    (B := ((107821543779209/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504259500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447450336187043/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611901921122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504259500001 : ℝ)) (s := (0.863552173675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613818754678 : ℝ) ≤ 0.687578519199 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613818754678 : ℝ)) (Q := (0.613818754678 : ℝ))
      (s := (0.789446981378 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782487876952 : ℝ)) (R := (0.783021842579 : ℝ)) (Q2 := (0.613818754678 : ℝ)) (T := (0.829673479131 : ℝ))
    (B := ((3447450336187043/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503068150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (43057680229743/62500000000000) := by
  have hk1 : kappa q ≤ 0.611105010733 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503068150001 : ℝ)) (s := (0.864246745123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613020395645 : ℝ) ≤ 0.687009271258 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613020395645 : ℝ)) (Q := (0.613020395645 : ℝ))
      (s := (0.790067082294 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781978495349 : ℝ)) (R := (0.782512460976 : ℝ)) (Q2 := (0.613020395645 : ℝ)) (T := (0.829329963664 : ℝ))
    (B := ((43057680229743/62500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501876800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3441781642482273/5000000000000000) := by
  have hk1 : kappa q ≤ 0.610308638826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501876800001 : ℝ)) (s := (0.864939117870 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612222575717 : ℝ) ≤ 0.686440679057 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612222575717 : ℝ)) (Q := (0.612222575717 : ℝ))
      (s := (0.790685473360 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781469126250 : ℝ)) (R := (0.782003091877 : ℝ)) (Q2 := (0.612222575717 : ℝ)) (T := (0.828986701806 : ℝ))
    (B := ((3441781642482273/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500685450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1719476001742517/2500000000000000) := by
  have hk1 : kappa q ≤ 0.609512804807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500685450001 : ℝ)) (s := (0.865629297193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611425294300 : ℝ) ≤ 0.685872741389 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611425294300 : ℝ)) (Q := (0.611425294300 : ℝ))
      (s := (0.791302160676 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780959769298 : ℝ)) (R := (0.781493734925 : ℝ)) (Q2 := (0.611425294300 : ℝ)) (T := (0.828643693144 : ℝ))
    (B := ((1719476001742517/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499494100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872250992792399/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608717508081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499494100001 : ℝ)) (s := (0.866317288333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610628550799 : ℝ) ≤ 0.685305457046 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610628550799 : ℝ)) (Q := (0.610628550799 : ℝ))
      (s := (0.791917150307 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780450424138 : ℝ)) (R := (0.780984389765 : ℝ)) (Q2 := (0.610628550799 : ℝ)) (T := (0.828300937261 : ℝ))
    (B := ((6872250992792399/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498302750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (858325529060779/1250000000000000) := by
  have hk1 : kappa q ≤ 0.607922748060 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498302750001 : ℝ)) (s := (0.867003096501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609832344624 : ℝ) ≤ 0.684738824825 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609832344624 : ℝ)) (Q := (0.609832344624 : ℝ))
      (s := (0.792530448280 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779941090414 : ℝ)) (R := (0.780475056041 : ℝ)) (Q2 := (0.609832344624 : ℝ)) (T := (0.827958433746 : ℝ))
    (B := ((858325529060779/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497111400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6860963716143779/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607128524156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497111400001 : ℝ)) (s := (0.867686726872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609036675186 : ℝ) ≤ 0.684172843527 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609036675186 : ℝ)) (Q := (0.609036675186 : ℝ))
      (s := (0.793142060591 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779431767772 : ℝ)) (R := (0.779965733399 : ℝ)) (Q2 := (0.609036675186 : ℝ)) (T := (0.827616182185 : ℝ))
    (B := ((6860963716143779/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495920050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1371065886778909/2000000000000000) := by
  have hk1 : kappa q ≤ 0.606334835785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495920050001 : ℝ)) (s := (0.868368184590 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608241541898 : ℝ) ≤ 0.683607511958 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608241541898 : ℝ)) (Q := (0.608241541898 : ℝ))
      (s := (0.793751993201 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778922455858 : ℝ)) (R := (0.779456421485 : ℝ)) (Q2 := (0.608241541898 : ℝ)) (T := (0.827274182169 : ℝ))
    (B := ((1371065886778909/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494728700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849701375905107/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605541682366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494728700001 : ℝ)) (s := (0.869047474765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607446944182 : ℝ) ≤ 0.683042828929 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607446944182 : ℝ)) (Q := (0.607446944182 : ℝ))
      (s := (0.794360252030 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778413154322 : ℝ)) (R := (0.778947119949 : ℝ)) (Q2 := (0.607446944182 : ℝ)) (T := (0.826932433291 : ℝ))
    (B := ((6849701375905107/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493537350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (68440795323789/100000000000000) := by
  have hk1 : kappa q ≤ 0.604749063323 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493537350001 : ℝ)) (s := (0.869724602478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606652881458 : ℝ) ≤ 0.682478793254 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606652881458 : ℝ)) (Q := (0.606652881458 : ℝ))
      (s := (0.794966842969 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777903862812 : ℝ)) (R := (0.778437828439 : ℝ)) (Q2 := (0.606652881458 : ℝ)) (T := (0.826590935143 : ℝ))
    (B := ((68440795323789/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492346000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838463893555993/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603956978079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492346000001 : ℝ)) (s := (0.870399572773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605859353149 : ℝ) ≤ 0.681915403749 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605859353149 : ℝ)) (Q := (0.605859353149 : ℝ))
      (s := (0.795571771874 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777394580978 : ℝ)) (R := (0.777928546605 : ℝ)) (Q2 := (0.605859353149 : ℝ)) (T := (0.826249687320 : ℝ))
    (B := ((6838463893555993/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491154650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6832854449712879/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603165426065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491154650001 : ℝ)) (s := (0.871072390668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605066358687 : ℝ) ≤ 0.681352659242 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605066358687 : ℝ)) (Q := (0.605066358687 : ℝ))
      (s := (0.796175044564 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776885308473 : ℝ)) (R := (0.777419274100 : ℝ)) (Q2 := (0.605066358687 : ℝ)) (T := (0.825908689421 : ℝ))
    (B := ((6832854449712879/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489963300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827251191162259/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602374406710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489963300001 : ℝ)) (s := (0.871743061144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604273897496 : ℝ) ≤ 0.680790558555 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604273897496 : ℝ)) (Q := (0.604273897496 : ℝ))
      (s := (0.796776666831 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776376044946 : ℝ)) (R := (0.776910010573 : ℝ)) (Q2 := (0.604273897496 : ℝ)) (T := (0.825567941041 : ℝ))
    (B := ((6827251191162259/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488771950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (682165410825283/1000000000000000) := by
  have hk1 : kappa q ≤ 0.601583919451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488771950001 : ℝ)) (s := (0.872411589156 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603481969014 : ℝ) ≤ 0.680229100521 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603481969014 : ℝ)) (Q := (0.603481969014 : ℝ))
      (s := (0.797376644426 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775866790053 : ℝ)) (R := (0.776400755680 : ℝ)) (Q2 := (0.603481969014 : ℝ)) (T := (0.825227441783 : ℝ))
    (B := ((682165410825283/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487580600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816063191369077/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600793963725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487580600001 : ℝ)) (s := (0.873077979624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602690572676 : ℝ) ≤ 0.679668283974 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602690572676 : ℝ)) (Q := (0.602690572676 : ℝ))
      (s := (0.797974983072 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775357543447 : ℝ)) (R := (0.775891509074 : ℝ)) (Q2 := (0.602690572676 : ℝ)) (T := (0.824887191246 : ℝ))
    (B := ((6816063191369077/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486389250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810478430931063/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600004538972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486389250001 : ℝ)) (s := (0.873742237439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601899707924 : ℝ) ≤ 0.679108107757 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601899707924 : ℝ)) (Q := (0.601899707924 : ℝ))
      (s := (0.798571688455 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774848304785 : ℝ)) (R := (0.775382270412 : ℝ)) (Q2 := (0.601899707924 : ℝ)) (T := (0.824547189037 : ℝ))
    (B := ((6810478430931063/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485197900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402449908697111/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599215644636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485197900001 : ℝ)) (s := (0.874404367461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601109374196 : ℝ) ≤ 0.678548570709 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601109374196 : ℝ)) (Q := (0.601109374196 : ℝ))
      (s := (0.799166766235 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774339073721 : ℝ)) (R := (0.774873039348 : ℝ)) (Q2 := (0.601109374196 : ℝ)) (T := (0.824207434757 : ℝ))
    (B := ((3402449908697111/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484006550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399663670624579/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598427280166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484006550001 : ℝ)) (s := (0.875064374522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600319570945 : ℝ) ≤ 0.677989671683 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600319570945 : ℝ)) (Q := (0.600319570945 : ℝ))
      (s := (0.799760222030 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773829849916 : ℝ)) (R := (0.774363815543 : ℝ)) (Q2 := (0.600319570945 : ℝ)) (T := (0.823867928016 : ℝ))
    (B := ((3399663670624579/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482815200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1698440248255359/2500000000000000) := by
  have hk1 : kappa q ≤ 0.597639445009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482815200001 : ℝ)) (s := (0.875722263420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599530297614 : ℝ) ≤ 0.677431409528 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599530297614 : ℝ)) (Q := (0.599530297614 : ℝ))
      (s := (0.800352061435 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773320633026 : ℝ)) (R := (0.773854598653 : ℝ)) (Q2 := (0.599530297614 : ℝ)) (T := (0.823528668422 : ℝ))
    (B := ((1698440248255359/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481623850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3394100381635693/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596852138620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481623850001 : ℝ)) (s := (0.876378038926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598741553659 : ℝ) ≤ 0.676873783103 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598741553659 : ℝ)) (Q := (0.598741553659 : ℝ))
      (s := (0.800942290008 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772811422713 : ℝ)) (R := (0.773345388340 : ℝ)) (Q2 := (0.598741553659 : ℝ)) (T := (0.823189655585 : ℝ))
    (B := ((3394100381635693/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480432500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782646642593899/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596065360454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480432500001 : ℝ)) (s := (0.877031705780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597953338532 : ℝ) ≤ 0.676316791267 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597953338532 : ℝ)) (Q := (0.597953338532 : ℝ))
      (s := (0.801530913277 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772302218636 : ℝ)) (R := (0.772836184263 : ℝ)) (Q2 := (0.597953338532 : ℝ)) (T := (0.822850889116 : ℝ))
    (B := ((6782646642593899/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479241150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (847137327702279/1250000000000000) := by
  have hk1 : kappa q ≤ 0.595279109971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479241150001 : ℝ)) (s := (0.877683268695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597165651692 : ℝ) ≤ 0.675760432885 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597165651692 : ℝ)) (Q := (0.597165651692 : ℝ))
      (s := (0.802117936740 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771793020457 : ℝ)) (R := (0.772326986084 : ℝ)) (Q2 := (0.597165651692 : ℝ)) (T := (0.822512368630 : ℝ))
    (B := ((847137327702279/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12975 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478049800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771556691007809/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594493386633 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478049800001 : ℝ)) (s := (0.878332732351 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596378492603 : ℝ) ≤ 0.675204706828 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596378492603 : ℝ)) (Q := (0.596378492603 : ℝ))
      (s := (0.802703365859 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771283827841 : ℝ)) (R := (0.771817793468 : ℝ)) (Q2 := (0.596378492603 : ℝ)) (T := (0.822174093743 : ℝ))
    (B := ((6771556691007809/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S25
namespace BstLean.Part269.S25
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12975 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.051919143187 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S25.wn_upper (by omega : 12975 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010484242328 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035424387669)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010484242328 + 2 * 0.737676 / 12975) := by gcongr
    _ ≤ (0.051919143187 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12975 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12975 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.907857498945 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12975 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.907857498945 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12975 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003274156000 + 0.003221457154 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003274156000 + 0.003221457154 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.907857498945 ≤ R)
    (hB : (X + 0.051919143187 + R + 0.008390678547) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008390678547 := by
    convert (BstLean.Part269.S25.finite_centre_upper (by omega : 12975 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (84662733863/1000000000000)
  | 2 => (85591441763/1000000000000)
  | 3 => (21629090989/250000000000)
  | 4 => (87438466021/1000000000000)
  | 5 => (22089732297/250000000000)
  | 6 => (89279184017/1000000000000)
  | 7 => (5637559223/62500000000)
  | 8 => (22781566037/250000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003274156000 + 0.003221457154 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218447888076 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010849712265 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003274156000 + 0.003221457154 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220021946706 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010963454682 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003274156000 + 0.003221457154 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221575394074 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011076821416 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003274156000 + 0.003221457154 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223108442728 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011189820705 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003274156000 + 0.003221457154 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224621299789 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011302460547 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003274156000 + 0.003221457154 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226114165462 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011414748596 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003274156000 + 0.003221457154 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227587234936 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011526692299 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12975 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003274156000 + 0.003221457154 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229040696929 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011638298782 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12975 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g) :
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

end BstLean.Part269.S25

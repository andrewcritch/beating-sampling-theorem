import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S24
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12950 ≤ n) : wn n ≤ 1.035458862322 := by
  have hnR : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.798066767410 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.798066767410 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035458862322 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12950 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12950 + 24 / (12950 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12950 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008398808221 : ℝ) := by
  have hnR : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.798066767410 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12950 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035458862322 * (81 / 1000 / 12950)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035458862322 * n *
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
        4 * (1 / 2.506628) * 1.035458862322 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035458862322 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035458862322 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12950)) / 113.798066767410 := by gcongr
    _ ≤ (0.008398808221 : ℝ) := by norm_num

end BstLean.Part269.S24
namespace BstLean.Part269.S24
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12950 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12950 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12950 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12950 + 0.008398808221 / 113.798066767410) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12950 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12950 := by gcongr
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
  have hn : (113.798066767410 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S24.finite_centre_upper (by omega : 12950 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528086500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7009733064877317/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627954155981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528086500001 : ℝ)) (s := (0.849190584332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629902477656 : ℝ) ≤ 0.699104801594 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629902477656 : ℝ)) (Q := (0.629902477656 : ℝ))
      (s := (0.776674235857 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792679163576 : ℝ)) (R := (0.793214160024 : ℝ)) (Q2 := (0.629902477656 : ℝ)) (T := (0.836598728565 : ℝ))
    (B := ((7009733064877317/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526895150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (437745833517617/625000000000000) := by
  have hk1 : kappa q ≤ 0.627146345960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526895150001 : ℝ)) (s := (0.849930291792 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629093205225 : ℝ) ≤ 0.698522176483 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629093205225 : ℝ)) (Q := (0.629093205225 : ℝ))
      (s := (0.777329877941 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792169455576 : ℝ)) (R := (0.792704452024 : ℝ)) (Q2 := (0.629093205225 : ℝ)) (T := (0.836250050498 : ℝ))
    (B := ((437745833517617/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525703800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1749535025082673/2500000000000000) := by
  have hk1 : kappa q ≤ 0.626339086996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525703800001 : ℝ)) (s := (0.850667687564 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628284484496 : ℝ) ≤ 0.697940232206 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628284484496 : ℝ)) (Q := (0.628284484496 : ℝ))
      (s := (0.777983680126 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791659767440 : ℝ)) (R := (0.792194763888 : ℝ)) (Q2 := (0.628284484496 : ℝ)) (T := (0.835901634694 : ℝ))
    (B := ((1749535025082673/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524512450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6992353346192539/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625532378429 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524512450001 : ℝ)) (s := (0.851402777653 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627476314809 : ℝ) ≤ 0.697358967469 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627476314809 : ℝ)) (Q := (0.627476314809 : ℝ))
      (s := (0.778635649296 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791150098790 : ℝ)) (R := (0.791685095238 : ℝ)) (Q2 := (0.627476314809 : ℝ)) (T := (0.835553480706 : ℝ))
    (B := ((6992353346192539/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523321100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (698657306307911/1000000000000000) := by
  have hk1 : kappa q ≤ 0.624726219604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523321100001 : ℝ)) (s := (0.852135568026 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668695508 : ℝ) ≤ 0.696778380984 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668695508 : ℝ)) (Q := (0.626668695508 : ℝ))
      (s := (0.779285792294 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790640449250 : ℝ)) (R := (0.791175445698 : ℝ)) (Q2 := (0.626668695508 : ℝ)) (T := (0.835205588091 : ℝ))
    (B := ((698657306307911/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522129750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6980799240244767/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623920609872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522129750001 : ℝ)) (s := (0.852866064611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625861625944 : ℝ) ≤ 0.696198471468 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625861625944 : ℝ)) (Q := (0.625861625944 : ℝ))
      (s := (0.779934115917 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790130818446 : ℝ)) (R := (0.790665814894 : ℝ)) (Q2 := (0.625861625944 : ℝ)) (T := (0.834857956404 : ℝ))
    (B := ((6980799240244767/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520938400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (697503186698627/1000000000000000) := by
  have hk1 : kappa q ≤ 0.623115548582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520938400001 : ℝ)) (s := (0.853594273297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625055105465 : ℝ) ≤ 0.695619237638 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625055105465 : ℝ)) (Q := (0.625055105465 : ℝ))
      (s := (0.780580626926 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789621206003 : ℝ)) (R := (0.790156202451 : ℝ)) (Q2 := (0.625055105465 : ℝ)) (T := (0.834510585204 : ℝ))
    (B := ((697503186698627/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519747050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969270932642511/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622311035089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519747050001 : ℝ)) (s := (0.854320199934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624249133421 : ℝ) ≤ 0.695040678216 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624249133421 : ℝ)) (Q := (0.624249133421 : ℝ))
      (s := (0.781225332042 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789111611545 : ℝ)) (R := (0.789646607993 : ℝ)) (Q2 := (0.624249133421 : ℝ)) (T := (0.834163474049 : ℝ))
    (B := ((6969270932642511/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518555700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (435219776662141/625000000000000) := by
  have hk1 : kappa q ≤ 0.621507068752 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518555700001 : ℝ)) (s := (0.855043850336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623443709175 : ℝ) ≤ 0.694462791932 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623443709175 : ℝ)) (Q := (0.623443709175 : ℝ))
      (s := (0.781868237935 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788602034704 : ℝ)) (R := (0.789137031152 : ℝ)) (Q2 := (0.623443709175 : ℝ)) (T := (0.833816622500 : ℝ))
    (B := ((435219776662141/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517364350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6957768338263879/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620703648931 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517364350001 : ℝ)) (s := (0.855765230276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622638832081 : ℝ) ≤ 0.693885577515 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622638832081 : ℝ)) (Q := (0.622638832081 : ℝ))
      (s := (0.782509351245 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788092475105 : ℝ)) (R := (0.788627471553 : ℝ)) (Q2 := (0.622638832081 : ℝ)) (T := (0.833470030119 : ℝ))
    (B := ((6957768338263879/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516173000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952026657115107/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619900774988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516173000001 : ℝ)) (s := (0.856484345491 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621834501504 : ℝ) ≤ 0.693309033700 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621834501504 : ℝ)) (Q := (0.621834501504 : ℝ))
      (s := (0.783148678566 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787582932379 : ℝ)) (R := (0.788117928827 : ℝ)) (Q2 := (0.621834501504 : ℝ)) (T := (0.833123696468 : ℝ))
    (B := ((6952026657115107/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514981650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473145686326383/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619098446292 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514981650001 : ℝ)) (s := (0.857201201681 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621030716811 : ℝ) ≤ 0.692733159229 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621030716811 : ℝ)) (Q := (0.621030716811 : ℝ))
      (s := (0.783786226453 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787073406157 : ℝ)) (R := (0.787608402605 : ℝ)) (Q2 := (0.621030716811 : ℝ)) (T := (0.832777621116 : ℝ))
    (B := ((3473145686326383/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513790300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1735140618605631/2500000000000000) := by
  have hk1 : kappa q ≤ 0.618296662211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513790300001 : ℝ)) (s := (0.857915804509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620227477366 : ℝ) ≤ 0.692157952841 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620227477366 : ℝ)) (Q := (0.620227477366 : ℝ))
      (s := (0.784422001426 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786563896068 : ℝ)) (R := (0.787098892516 : ℝ)) (Q2 := (0.620227477366 : ℝ)) (T := (0.832431803625 : ℝ))
    (B := ((1735140618605631/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512598950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3467419976005321/5000000000000000) := by
  have hk1 : kappa q ≤ 0.617495422118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512598950001 : ℝ)) (s := (0.858628159600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619424782544 : ℝ) ≤ 0.691583413286 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619424782544 : ℝ)) (Q := (0.619424782544 : ℝ))
      (s := (0.785056009958 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786054401746 : ℝ)) (R := (0.786589398194 : ℝ)) (Q2 := (0.619424782544 : ℝ)) (T := (0.832086243564 : ℝ))
    (B := ((3467419976005321/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511407600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3464561897521863/5000000000000000) := by
  have hk1 : kappa q ≤ 0.616694725391 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511407600001 : ℝ)) (s := (0.859338272546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618622631721 : ℝ) ≤ 0.691009539315 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618622631721 : ℝ)) (Q := (0.618622631721 : ℝ))
      (s := (0.785688258486 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785544922826 : ℝ)) (R := (0.786079919274 : ℝ)) (Q2 := (0.618622631721 : ℝ)) (T := (0.831740940505 : ℝ))
    (B := ((3464561897521863/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510216250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3461706996594239/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615894571407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510216250001 : ℝ)) (s := (0.860046148899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617821024273 : ℝ) ≤ 0.690436329684 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617821024273 : ℝ)) (Q := (0.617821024273 : ℝ))
      (s := (0.786318753412 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785035458940 : ℝ)) (R := (0.785570455388 : ℝ)) (Q2 := (0.617821024273 : ℝ)) (T := (0.831395894016 : ℝ))
    (B := ((3461706996594239/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509024900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6917710536151451/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615094959549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509024900001 : ℝ)) (s := (0.860751794178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617019959583 : ℝ) ≤ 0.689863783153 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617019959583 : ℝ)) (Q := (0.617019959583 : ℝ))
      (s := (0.786947501093 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784526009726 : ℝ)) (R := (0.785061006174 : ℝ)) (Q2 := (0.617019959583 : ℝ)) (T := (0.831051103672 : ℝ))
    (B := ((6917710536151451/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507833550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912013413678809/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614295889201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507833550001 : ℝ)) (s := (0.861455213864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616219437030 : ℝ) ≤ 0.689291898483 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616219437030 : ℝ)) (Q := (0.616219437030 : ℝ))
      (s := (0.787574507858 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784016574817 : ℝ)) (R := (0.784551571265 : ℝ)) (Q2 := (0.616219437030 : ℝ)) (T := (0.830706569044 : ℝ))
    (B := ((6912013413678809/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506642200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1381264523111217/2000000000000000) := by
  have hk1 : kappa q ≤ 0.613497359753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506642200001 : ℝ)) (s := (0.862156413407 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615419456007 : ℝ) ≤ 0.688720674445 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615419456007 : ℝ)) (Q := (0.615419456007 : ℝ))
      (s := (0.788199779985 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783507153854 : ℝ)) (R := (0.784042150302 : ℝ)) (Q2 := (0.615419456007 : ℝ)) (T := (0.830362289710 : ℝ))
    (B := ((1381264523111217/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505450850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450319065803971/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612699370595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505450850001 : ℝ)) (s := (0.862855398218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614620015901 : ℝ) ≤ 0.688150109809 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614620015901 : ℝ)) (Q := (0.614620015901 : ℝ))
      (s := (0.788823323726 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782997746473 : ℝ)) (R := (0.783532742921 : ℝ)) (Q2 := (0.614620015901 : ℝ)) (T := (0.830018265246 : ℝ))
    (B := ((3450319065803971/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504259500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447479975848969/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611901921122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504259500001 : ℝ)) (s := (0.863552173675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613821116106 : ℝ) ≤ 0.687580203353 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613821116106 : ℝ)) (Q := (0.613821116106 : ℝ))
      (s := (0.789445145291 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782488352315 : ℝ)) (R := (0.783023348763 : ℝ)) (Q2 := (0.613821116106 : ℝ)) (T := (0.829674495231 : ℝ))
    (B := ((3447479975848969/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503068150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889288065728289/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611105010733 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503068150001 : ℝ)) (s := (0.864246745123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613022756022 : ℝ) ≤ 0.687010953859 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613022756022 : ℝ)) (Q := (0.613022756022 : ℝ))
      (s := (0.790065250850 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781978971022 : ℝ)) (R := (0.782513967470 : ℝ)) (Q2 := (0.613022756022 : ℝ)) (T := (0.829330979247 : ℝ))
    (B := ((6889288065728289/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501876800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3441811231819821/5000000000000000) := by
  have hk1 : kappa q ≤ 0.610308638826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501876800001 : ℝ)) (s := (0.864939117870 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612224935042 : ℝ) ≤ 0.686442360107 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612224935042 : ℝ)) (Q := (0.612224935042 : ℝ))
      (s := (0.790683646545 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781469602232 : ℝ)) (R := (0.782004598680 : ℝ)) (Q2 := (0.612224935042 : ℝ)) (T := (0.828987716873 : ℝ))
    (B := ((3441811231819821/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500685450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3438981567705419/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609512804807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500685450001 : ℝ)) (s := (0.865629297193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611427652575 : ℝ) ≤ 0.685874420890 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611427652575 : ℝ)) (Q := (0.611427652575 : ℝ))
      (s := (0.791300338473 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780960245591 : ℝ)) (R := (0.781495242039 : ℝ)) (Q2 := (0.611427652575 : ℝ)) (T := (0.828644707695 : ℝ))
    (B := ((3438981567705419/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499494100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (26844961215073/39062500000000) := by
  have hk1 : kappa q ≤ 0.608717508081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499494100001 : ℝ)) (s := (0.866317288333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610630908022 : ℝ) ≤ 0.685307134999 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610630908022 : ℝ)) (Q := (0.610630908022 : ℝ))
      (s := (0.791915332702 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780450900741 : ℝ)) (R := (0.780985897189 : ℝ)) (Q2 := (0.610630908022 : ℝ)) (T := (0.828301951298 : ℝ))
    (B := ((26844961215073/39062500000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498302750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1373332652127549/2000000000000000) := by
  have hk1 : kappa q ≤ 0.607922748060 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498302750001 : ℝ)) (s := (0.867003096501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609834700797 : ℝ) ≤ 0.684740501234 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609834700797 : ℝ)) (Q := (0.609834700797 : ℝ))
      (s := (0.792528635258 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779941567329 : ℝ)) (R := (0.780476563777 : ℝ)) (Q2 := (0.609834700797 : ℝ)) (T := (0.827959447268 : ℝ))
    (B := ((1373332652127549/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497111400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (85762783678001/125000000000000) := by
  have hk1 : kappa q ≤ 0.607128524156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497111400001 : ℝ)) (s := (0.867686726872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609039030307 : ℝ) ≤ 0.684174518392 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609039030307 : ℝ)) (Q := (0.609039030307 : ℝ))
      (s := (0.793140252139 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779432244998 : ℝ)) (R := (0.779967241446 : ℝ)) (Q2 := (0.609039030307 : ℝ)) (T := (0.827617195192 : ℝ))
    (B := ((85762783678001/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495920050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3427694180997529/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606334835785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495920050001 : ℝ)) (s := (0.868368184590 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608243895969 : ℝ) ≤ 0.683609185282 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608243895969 : ℝ)) (Q := (0.608243895969 : ℝ))
      (s := (0.793750189302 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778922933397 : ℝ)) (R := (0.779457929845 : ℝ)) (Q2 := (0.608243895969 : ℝ)) (T := (0.827275194663 : ℝ))
    (B := ((3427694180997529/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494728700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6849760254069119/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605541682366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494728700001 : ℝ)) (s := (0.869047474765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607449297202 : ℝ) ≤ 0.683044500714 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607449297202 : ℝ)) (Q := (0.607449297202 : ℝ))
      (s := (0.794358452671 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778413632173 : ℝ)) (R := (0.778948628621 : ℝ)) (Q2 := (0.607449297202 : ℝ)) (T := (0.826933445272 : ℝ))
    (B := ((6849760254069119/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493537350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844138360665559/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604749063323 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493537350001 : ℝ)) (s := (0.869724602478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606655233427 : ℝ) ≤ 0.682480463501 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606655233427 : ℝ)) (Q := (0.606655233427 : ℝ))
      (s := (0.794965048135 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777904340976 : ℝ)) (R := (0.778439337424 : ℝ)) (Q2 := (0.606655233427 : ℝ)) (T := (0.826591946611 : ℝ))
    (B := ((6844138360665559/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492346000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838522672024309/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603956978079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492346000001 : ℝ)) (s := (0.870399572773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605861704069 : ℝ) ≤ 0.681917072463 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605861704069 : ℝ)) (Q := (0.605861704069 : ℝ))
      (s := (0.795569981550 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777395059456 : ℝ)) (R := (0.777930055904 : ℝ)) (Q2 := (0.605861704069 : ℝ)) (T := (0.826250698276 : ℝ))
    (B := ((6838522672024309/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491154650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416456589210863/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603165426065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491154650001 : ℝ)) (s := (0.871072390668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605068708553 : ℝ) ≤ 0.681354326420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605068708553 : ℝ)) (Q := (0.605068708553 : ℝ))
      (s := (0.796173258739 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776885787263 : ℝ)) (R := (0.777420783711 : ℝ)) (Q2 := (0.605068708553 : ℝ)) (T := (0.825909699864 : ℝ))
    (B := ((3416456589210863/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489963300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (54618478961363/80000000000000) := by
  have hk1 : kappa q ≤ 0.602374406710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489963300001 : ℝ)) (s := (0.871743061144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604276246313 : ℝ) ≤ 0.680792224202 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604276246313 : ℝ)) (Q := (0.604276246313 : ℝ))
      (s := (0.796774885487 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776376524051 : ℝ)) (R := (0.776911520499 : ℝ)) (Q2 := (0.604276246313 : ℝ)) (T := (0.825568950973 : ℝ))
    (B := ((54618478961363/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488771950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821712737618817/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601583919451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488771950001 : ℝ)) (s := (0.872411589156 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603484316780 : ℝ) ≤ 0.680230764639 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603484316780 : ℝ)) (Q := (0.603484316780 : ℝ))
      (s := (0.797374867551 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775867269472 : ℝ)) (R := (0.776402265920 : ℝ)) (Q2 := (0.603484316780 : ℝ)) (T := (0.825228451204 : ℝ))
    (B := ((6821712737618817/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487580600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1704030442787851/2500000000000000) := by
  have hk1 : kappa q ≤ 0.600793963725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487580600001 : ℝ)) (s := (0.873077979624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602692919391 : ℝ) ≤ 0.679669946564 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602692919391 : ℝ)) (Q := (0.602692919391 : ℝ))
      (s := (0.797973210651 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775358023181 : ℝ)) (R := (0.775893019629 : ℝ)) (Q2 := (0.602692919391 : ℝ)) (T := (0.824888200156 : ℝ))
    (B := ((1704030442787851/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486389250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405268480594031/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600004538972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486389250001 : ℝ)) (s := (0.873742237439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601902053588 : ℝ) ≤ 0.679109768821 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601902053588 : ℝ)) (Q := (0.601902053588 : ℝ))
      (s := (0.798569920475 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774848784834 : ℝ)) (R := (0.775383781282 : ℝ)) (Q2 := (0.601902053588 : ℝ)) (T := (0.824548197436 : ℝ))
    (B := ((3405268480594031/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485197900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1360991659636819/2000000000000000) := by
  have hk1 : kappa q ≤ 0.599215644636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485197900001 : ℝ)) (s := (0.874404367461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601111718810 : ℝ) ≤ 0.678550230250 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601111718810 : ℝ)) (Q := (0.601111718810 : ℝ))
      (s := (0.799165002681 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774339554086 : ℝ)) (R := (0.774874550534 : ℝ)) (Q2 := (0.601111718810 : ℝ)) (T := (0.824208442647 : ℝ))
    (B := ((1360991659636819/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484006550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1699846443157493/2500000000000000) := by
  have hk1 : kappa q ≤ 0.598427280166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484006550001 : ℝ)) (s := (0.875064374522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600321914509 : ℝ) ≤ 0.677991329703 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600321914509 : ℝ)) (Q := (0.600321914509 : ℝ))
      (s := (0.799758462888 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773830330598 : ℝ)) (R := (0.774365327046 : ℝ)) (Q2 := (0.600321914509 : ℝ)) (T := (0.823868935398 : ℝ))
    (B := ((1699846443157493/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482815200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793819375051127/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597639445009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482815200001 : ℝ)) (s := (0.875722263420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599532640127 : ℝ) ≤ 0.677433066028 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599532640127 : ℝ)) (Q := (0.599532640127 : ℝ))
      (s := (0.800350306693 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773321114024 : ℝ)) (R := (0.773856110472 : ℝ)) (Q2 := (0.599532640127 : ℝ)) (T := (0.823529675294 : ℝ))
    (B := ((6793819375051127/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481623850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3394129548003879/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596852138620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481623850001 : ℝ)) (s := (0.876378038926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598743895121 : ℝ) ≤ 0.676875438084 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598743895121 : ℝ)) (Q := (0.598743895121 : ℝ))
      (s := (0.800940539651 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772811904028 : ℝ)) (R := (0.773346900476 : ℝ)) (Q2 := (0.598743895121 : ℝ)) (T := (0.823190661948 : ℝ))
    (B := ((3394129548003879/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480432500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782704926094627/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596065360454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480432500001 : ℝ)) (s := (0.877031705780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597955678943 : ℝ) ≤ 0.676318444732 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597955678943 : ℝ)) (Q := (0.597955678943 : ℝ))
      (s := (0.801529167293 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772302700268 : ℝ)) (R := (0.772837696716 : ℝ)) (Q2 := (0.597955678943 : ℝ)) (T := (0.822851894972 : ℝ))
    (B := ((6782704926094627/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479241150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3388578427970429/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595279109971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479241150001 : ℝ)) (s := (0.877683268695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597167991053 : ℝ) ≤ 0.675762084835 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597167991053 : ℝ)) (Q := (0.597167991053 : ℝ))
      (s := (0.802116195113 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771793502407 : ℝ)) (R := (0.772328498855 : ℝ)) (Q2 := (0.597167991053 : ℝ)) (T := (0.822513373978 : ℝ))
    (B := ((3388578427970429/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12950 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478049800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771614876209747/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594493386633 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478049800001 : ℝ)) (s := (0.878332732351 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596380830913 : ℝ) ≤ 0.675206357266 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596380830913 : ℝ)) (Q := (0.596380830913 : ℝ))
      (s := (0.802701628577 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771284310109 : ℝ)) (R := (0.771819306557 : ℝ)) (Q2 := (0.596380830913 : ℝ)) (T := (0.822175098583 : ℝ))
    (B := ((6771614876209747/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S24
namespace BstLean.Part269.S24
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12950 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.051969771981 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S24.wn_upper (by omega : 12950 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010494357374 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035458862322)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010494357374 + 2 * 0.737676 / 12950) := by gcongr
    _ ≤ (0.051969771981 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12950 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12950 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.798066767410 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12950 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.798066767410 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12950 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003279469477 + 0.003227897328 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003279469477 + 0.003227897328 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.798066767410 ≤ R)
    (hB : (X + 0.051969771981 + R + 0.008398808221) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008398808221 := by
    convert (BstLean.Part269.S24.finite_centre_upper (by omega : 12950 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (42364236993/500000000000)
  | 2 => (85658055671/1000000000000)
  | 3 => (5411499093/62500000000)
  | 4 => (2187681507/25000000000)
  | 5 => (88429098229/1000000000000)
  | 6 => (17870194657/200000000000)
  | 7 => (90274653119/1000000000000)
  | 8 => (1140028009/12500000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003279469477 + 0.003227897328 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218467042038 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010860179911 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003279469477 + 0.003227897328 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220041068967 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010974032065 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003279469477 + 0.003227897328 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221594486859 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011087508174 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003279469477 + 0.003227897328 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223127508191 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011200616482 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003279469477 + 0.003227897328 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224640340013 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011313364998 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003279469477 + 0.003227897328 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226133182467 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011425761381 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003279469477 + 0.003227897328 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227606230678 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011537813085 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12950 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003279469477 + 0.003227897328 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229059673305 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011649527244 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12950 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g) :
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

end BstLean.Part269.S24

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S34
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 13200 ≤ n) : wn n ≤ 1.035118561495 := by
  have hnR : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (114.891252930760 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (114.891252930760 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035118561495 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 13200 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 13200 + 24 / (13200 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 13200 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008318556854 : ℝ) := by
  have hnR : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (114.891252930760 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (13200 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035118561495 * (81 / 1000 / 13200)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035118561495 * n *
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
        4 * (1 / 2.506628) * 1.035118561495 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035118561495 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035118561495 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 13200)) / 114.891252930760 := by gcongr
    _ ≤ (0.008318556854 : ℝ) := by norm_num

end BstLean.Part269.S34
namespace BstLean.Part269.S34
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 13200 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 13200 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 13200 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 13200 + 0.008318556854 / 114.891252930760) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 13200 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 13200 := by gcongr
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
  have hn : (114.891252930760 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S34.finite_centre_upper (by omega : 13200 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528086500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7009140355900461/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627954155981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528086500001 : ℝ)) (s := (0.849190584332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629879059375 : ℝ) ≤ 0.699087937917 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629879059375 : ℝ)) (Q := (0.629879059375 : ℝ))
      (s := (0.776693228091 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792674551036 : ℝ)) (R := (0.793199414976 : ℝ)) (Q2 := (0.629879059375 : ℝ)) (T := (0.836588638364 : ℝ))
    (B := ((7009140355900461/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526895150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3501670567193197/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627146345960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526895150001 : ℝ)) (s := (0.849930291792 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629069797282 : ℝ) ≤ 0.698505328467 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629069797282 : ℝ)) (Q := (0.629069797282 : ℝ))
      (s := (0.777348821411 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792164840068 : ℝ)) (R := (0.792689704008 : ℝ)) (Q2 := (0.629069797282 : ℝ)) (T := (0.836239965464 : ℝ))
    (B := ((3501670567193197/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525703800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1399509680979201/2000000000000000) := by
  have hk1 : kappa q ≤ 0.626339086996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525703800001 : ℝ)) (s := (0.850667687564 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628261086889 : ℝ) ≤ 0.697923399829 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628261086889 : ℝ)) (Q := (0.628261086889 : ℝ))
      (s := (0.778002574997 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791655148960 : ℝ)) (R := (0.792180012900 : ℝ)) (Q2 := (0.628261086889 : ℝ)) (T := (0.835891554822 : ℝ))
    (B := ((1399509680979201/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524512450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6991762156599611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625532378429 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524512450001 : ℝ)) (s := (0.851402777653 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627452927541 : ℝ) ≤ 0.697342150714 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627452927541 : ℝ)) (Q := (0.627452927541 : ℝ))
      (s := (0.778654495730 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791145477336 : ℝ)) (R := (0.791670341276 : ℝ)) (Q2 := (0.627452927541 : ℝ)) (T := (0.835543405993 : ℝ))
    (B := ((6991762156599611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523321100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1746495594677613/2500000000000000) := by
  have hk1 : kappa q ≤ 0.624726219604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523321100001 : ℝ)) (s := (0.852135568026 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626645318578 : ℝ) ≤ 0.696761579830 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626645318578 : ℝ)) (Q := (0.626645318578 : ℝ))
      (s := (0.779304590456 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790635824817 : ℝ)) (R := (0.791160688757 : ℝ)) (Q2 := (0.626645318578 : ℝ)) (T := (0.835195518531 : ℝ))
    (B := ((1746495594677613/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522129750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1745052265121107/2500000000000000) := by
  have hk1 : kappa q ≤ 0.623920609872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522129750001 : ℝ)) (s := (0.852866064611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625838259349 : ℝ) ≤ 0.696181685893 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625838259349 : ℝ)) (Q := (0.625838259349 : ℝ))
      (s := (0.779952865971 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790126191030 : ℝ)) (R := (0.790651054970 : ℝ)) (Q2 := (0.625838259349 : ℝ)) (T := (0.834847891993 : ℝ))
    (B := ((1745052265121107/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520938400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6974442191219827/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623115548582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520938400001 : ℝ)) (s := (0.853594273297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625031749205 : ℝ) ≤ 0.695602467623 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625031749205 : ℝ)) (Q := (0.625031749205 : ℝ))
      (s := (0.780599329033 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789616575600 : ℝ)) (R := (0.790141439540 : ℝ)) (Q2 := (0.625031749205 : ℝ)) (T := (0.834500525937 : ℝ))
    (B := ((6974442191219827/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519747050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6968681760257063/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622311035089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519747050001 : ℝ)) (s := (0.854320199934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624225787497 : ℝ) ≤ 0.695023923741 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624225787497 : ℝ)) (Q := (0.624225787497 : ℝ))
      (s := (0.781243986361 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789106978152 : ℝ)) (R := (0.789631842092 : ℝ)) (Q2 := (0.624225787497 : ℝ)) (T := (0.834153419921 : ℝ))
    (B := ((6968681760257063/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518555700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6962927756978413/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621507068752 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518555700001 : ℝ)) (s := (0.855043850336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623420373586 : ℝ) ≤ 0.694446052978 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623420373586 : ℝ)) (Q := (0.623420373586 : ℝ))
      (s := (0.781886844626 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788597398317 : ℝ)) (R := (0.789122262257 : ℝ)) (Q2 := (0.623420373586 : ℝ)) (T := (0.833806573508 : ℝ))
    (B := ((6962927756978413/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517364350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1739295042701939/2500000000000000) := by
  have hk1 : kappa q ≤ 0.620703648931 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517364350001 : ℝ)) (s := (0.855765230276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622615506827 : ℝ) ≤ 0.693868854062 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622615506827 : ℝ)) (Q := (0.622615506827 : ℝ))
      (s := (0.782527910467 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788087835720 : ℝ)) (R := (0.788612699660 : ℝ)) (Q2 := (0.622615506827 : ℝ)) (T := (0.833459986257 : ℝ))
    (B := ((1739295042701939/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516173000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1737859747802579/2500000000000000) := by
  have hk1 : kappa q ≤ 0.619900774988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516173000001 : ℝ)) (s := (0.856484345491 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621811186586 : ℝ) ≤ 0.693292325729 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621811186586 : ℝ)) (Q := (0.621811186586 : ℝ))
      (s := (0.783167190476 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787578289993 : ℝ)) (R := (0.788103153933 : ℝ)) (Q2 := (0.621811186586 : ℝ)) (T := (0.833113657734 : ℝ))
    (B := ((1737859747802579/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514981650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6945704207692407/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619098446292 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514981650001 : ℝ)) (s := (0.857201201681 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621007412226 : ℝ) ≤ 0.692716466718 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621007412226 : ℝ)) (Q := (0.621007412226 : ℝ))
      (s := (0.783804691209 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787068760765 : ℝ)) (R := (0.787593624705 : ℝ)) (Q2 := (0.621007412226 : ℝ)) (T := (0.832767587502 : ℝ))
    (B := ((6945704207692407/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513790300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3469987904900589/5000000000000000) := by
  have hk1 : kappa q ≤ 0.618296662211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513790300001 : ℝ)) (s := (0.857915804509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620204183115 : ℝ) ≤ 0.692141275772 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620204183115 : ℝ)) (Q := (0.620204183115 : ℝ))
      (s := (0.784440419183 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786559247667 : ℝ)) (R := (0.787084111607 : ℝ)) (Q2 := (0.620204183115 : ℝ)) (T := (0.832421775129 : ℝ))
    (B := ((3469987904900589/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512598950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1733563446781091/2500000000000000) := by
  have hk1 : kappa q ≤ 0.617495422118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512598950001 : ℝ)) (s := (0.858628159600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619401498626 : ℝ) ≤ 0.691566751637 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619401498626 : ℝ)) (Q := (0.619401498626 : ℝ))
      (s := (0.785074380871 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786049750332 : ℝ)) (R := (0.786574614272 : ℝ)) (Q2 := (0.619401498626 : ℝ)) (T := (0.832076220180 : ℝ))
    (B := ((1733563446781091/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511407600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1732134532322509/2500000000000000) := by
  have hk1 : kappa q ≤ 0.616694725391 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511407600001 : ℝ)) (s := (0.859338272546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618599358136 : ℝ) ≤ 0.690992893069 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618599358136 : ℝ)) (Q := (0.618599358136 : ℝ))
      (s := (0.785706582710 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785540268395 : ℝ)) (R := (0.786065132335 : ℝ)) (Q2 := (0.618599358136 : ℝ)) (T := (0.831730922229 : ℝ))
    (B := ((1732134532322509/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510216250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6922828825966353/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615894571407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510216250001 : ℝ)) (s := (0.860046148899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617797761021 : ℝ) ≤ 0.690419698820 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617797761021 : ℝ)) (Q := (0.617797761021 : ℝ))
      (s := (0.786337031099 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785030801489 : ℝ)) (R := (0.785555665429 : ℝ)) (Q2 := (0.617797761021 : ℝ)) (T := (0.831385880844 : ℝ))
    (B := ((6922828825966353/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509024900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6917125866861319/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615094959549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509024900001 : ℝ)) (s := (0.860751794178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616996706663 : ℝ) ≤ 0.689847167651 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616996706663 : ℝ)) (Q := (0.616996706663 : ℝ))
      (s := (0.786965732397 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784521349250 : ℝ)) (R := (0.785046213190 : ℝ)) (Q2 := (0.616996706663 : ℝ)) (T := (0.831041095599 : ℝ))
    (B := ((6917125866861319/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507833550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6911429241722541/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614295889201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507833550001 : ℝ)) (s := (0.861455213864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616196194443 : ℝ) ≤ 0.689275298325 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616196194443 : ℝ)) (Q := (0.616196194443 : ℝ))
      (s := (0.787592692929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784011911313 : ℝ)) (R := (0.784536775253 : ℝ)) (Q2 := (0.616196194443 : ℝ)) (T := (0.830696566066 : ℝ))
    (B := ((6911429241722541/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506642200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6905738940336987/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613497359753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506642200001 : ℝ)) (s := (0.862156413407 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615396223751 : ℝ) ≤ 0.688704089609 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615396223751 : ℝ)) (Q := (0.615396223751 : ℝ))
      (s := (0.788217918975 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783502487317 : ℝ)) (R := (0.784027351257 : ℝ)) (Q2 := (0.615396223751 : ℝ)) (T := (0.830352291821 : ℝ))
    (B := ((6905738940336987/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505450850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900054952530749/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612699370595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505450850001 : ℝ)) (s := (0.862855398218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614596793977 : ℝ) ≤ 0.688133540278 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614596793977 : ℝ)) (Q := (0.614596793977 : ℝ))
      (s := (0.788841416784 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782993076901 : ℝ)) (R := (0.783517940841 : ℝ)) (Q2 := (0.614596793977 : ℝ)) (T := (0.830008272443 : ℝ))
    (B := ((6900054952530749/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504259500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6894377268168803/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611901921122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504259500001 : ℝ)) (s := (0.863552173675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613797904514 : ℝ) ≤ 0.687563649107 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613797904514 : ℝ)) (Q := (0.613797904514 : ℝ))
      (s := (0.789463192565 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782483679703 : ℝ)) (R := (0.783008543643 : ℝ)) (Q2 := (0.613797904514 : ℝ)) (T := (0.829664507510 : ℝ))
    (B := ((6894377268168803/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503068150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444352938577391/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611105010733 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503068150001 : ℝ)) (s := (0.864246745123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612999554761 : ℝ) ≤ 0.686994414878 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612999554761 : ℝ)) (Q := (0.612999554761 : ℝ))
      (s := (0.790083252489 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781974295366 : ℝ)) (R := (0.782499159306 : ℝ)) (Q2 := (0.612999554761 : ℝ)) (T := (0.829320996603 : ℝ))
    (B := ((3444352938577391/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501876800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (430190048089421/625000000000000) := by
  have hk1 : kappa q ≤ 0.610308638826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501876800001 : ℝ)) (s := (0.864939117870 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612201744113 : ℝ) ≤ 0.686425836372 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612201744113 : ℝ)) (Q := (0.612201744113 : ℝ))
      (s := (0.790701602696 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781464923529 : ℝ)) (R := (0.781989787469 : ℝ)) (Q2 := (0.612201744113 : ℝ)) (T := (0.828977739302 : ℝ))
    (B := ((430190048089421/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500685450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3438690967488453/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609512804807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500685450001 : ℝ)) (s := (0.865629297193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611404471975 : ℝ) ≤ 0.685857912381 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611404471975 : ℝ)) (Q := (0.611404471975 : ℝ))
      (s := (0.791318249284 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780955563836 : ℝ)) (R := (0.781480427776 : ℝ)) (Q2 := (0.611404471975 : ℝ)) (T := (0.828634735191 : ℝ))
    (B := ((3438690967488453/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499494100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (858966170476437/1250000000000000) := by
  have hk1 : kappa q ≤ 0.608717508081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499494100001 : ℝ)) (s := (0.866317288333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610607737753 : ℝ) ≤ 0.685290641696 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610607737753 : ℝ)) (Q := (0.610607737753 : ℝ))
      (s := (0.791933198317 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780446215931 : ℝ)) (R := (0.780971079871 : ℝ)) (Q2 := (0.610607737753 : ℝ)) (T := (0.828291983856 : ℝ))
    (B := ((858966170476437/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498302750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433041522995221/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607922748060 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498302750001 : ℝ)) (s := (0.867003096501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609811540857 : ℝ) ≤ 0.684724023118 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609811540857 : ℝ)) (Q := (0.609811540857 : ℝ))
      (s := (0.792546455824 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779936879459 : ℝ)) (R := (0.780461743399 : ℝ)) (Q2 := (0.609811540857 : ℝ)) (T := (0.827949484885 : ℝ))
    (B := ((3433041522995221/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497111400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430221485803597/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607128524156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497111400001 : ℝ)) (s := (0.867686726872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609015880698 : ℝ) ≤ 0.684158055446 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609015880698 : ℝ)) (Q := (0.609015880698 : ℝ))
      (s := (0.793158027797 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779427554065 : ℝ)) (R := (0.779952418005 : ℝ)) (Q2 := (0.609015880698 : ℝ)) (T := (0.827607237865 : ℝ))
    (B := ((3430221485803597/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495920050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (856851141349061/1250000000000000) := by
  have hk1 : kappa q ≤ 0.606334835785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495920050001 : ℝ)) (s := (0.868368184590 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608220756691 : ℝ) ≤ 0.683592737486 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608220756691 : ℝ)) (Q := (0.608220756691 : ℝ))
      (s := (0.793767920195 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778918239397 : ℝ)) (R := (0.779443103337 : ℝ)) (Q2 := (0.608220756691 : ℝ)) (T := (0.827265242386 : ℝ))
    (B := ((856851141349061/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494728700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (428073844607133/625000000000000) := by
  have hk1 : kappa q ≤ 0.605541682366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494728700001 : ℝ)) (s := (0.869047474765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607426168251 : ℝ) ≤ 0.683028068046 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607426168251 : ℝ)) (Q := (0.607426168251 : ℝ))
      (s := (0.794376138945 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778408935101 : ℝ)) (R := (0.778933799041 : ℝ)) (Q2 := (0.607426168251 : ℝ)) (T := (0.826923498039 : ℝ))
    (B := ((428073844607133/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493537350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1368712022115353/2000000000000000) := by
  have hk1 : kappa q ≤ 0.604749063323 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493537350001 : ℝ)) (s := (0.869724602478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606632114806 : ℝ) ≤ 0.682464045944 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606632114806 : ℝ)) (Q := (0.606632114806 : ℝ))
      (s := (0.794982689929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777899640829 : ℝ)) (R := (0.778424504769 : ℝ)) (Q2 := (0.606632114806 : ℝ)) (T := (0.826582004420 : ℝ))
    (B := ((1368712022115353/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492346000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6837944911621683/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603956978079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492346000001 : ℝ)) (s := (0.870399572773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605838595776 : ℝ) ≤ 0.681900669997 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605838595776 : ℝ)) (Q := (0.605838595776 : ℝ))
      (s := (0.795587579006 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777390356229 : ℝ)) (R := (0.777915220169 : ℝ)) (Q2 := (0.605838595776 : ℝ)) (T := (0.826240761122 : ℝ))
    (B := ((6837944911621683/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491154650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6832335907126581/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603165426065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491154650001 : ℝ)) (s := (0.871072390668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605045610591 : ℝ) ≤ 0.681337939028 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605045610591 : ℝ)) (Q := (0.605045610591 : ℝ))
      (s := (0.796190811995 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776881080954 : ℝ)) (R := (0.777405944894 : ℝ)) (Q2 := (0.605045610591 : ℝ)) (T := (0.825899767743 : ℝ))
    (B := ((6832335907126581/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489963300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6826733087405361/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602374406710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489963300001 : ℝ)) (s := (0.871743061144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604253158678 : ℝ) ≤ 0.680775851863 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604253158678 : ℝ)) (Q := (0.604253158678 : ℝ))
      (s := (0.796792394685 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776371814654 : ℝ)) (R := (0.776896678594 : ℝ)) (Q2 := (0.604253158678 : ℝ)) (T := (0.825559023880 : ℝ))
    (B := ((6826733087405361/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488771950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364227288561583/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601583919451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488771950001 : ℝ)) (s := (0.872411589156 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603461239475 : ℝ) ≤ 0.680214407335 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603461239475 : ℝ)) (Q := (0.603461239475 : ℝ))
      (s := (0.797392332828 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775862556985 : ℝ)) (R := (0.776387420925 : ℝ)) (Q2 := (0.603461239475 : ℝ)) (T := (0.825218529134 : ℝ))
    (B := ((1364227288561583/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487580600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3407772981859959/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600793963725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487580600001 : ℝ)) (s := (0.873077979624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602669852414 : ℝ) ≤ 0.679653604276 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602669852414 : ℝ)) (Q := (0.602669852414 : ℝ))
      (s := (0.797990632146 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775353307599 : ℝ)) (R := (0.775878171539 : ℝ)) (Q2 := (0.602669852414 : ℝ)) (T := (0.824878283106 : ℝ))
    (B := ((3407772981859959/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486389250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3404980820281307/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600004538972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486389250001 : ℝ)) (s := (0.873742237439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601878996938 : ℝ) ≤ 0.679093441529 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601878996938 : ℝ)) (Q := (0.601878996938 : ℝ))
      (s := (0.798587298325 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774844066152 : ℝ)) (R := (0.775368930092 : ℝ)) (Q2 := (0.601878996938 : ℝ)) (T := (0.824538285401 : ℝ))
    (B := ((3404980820281307/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485197900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804383463792617/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599215644636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485197900001 : ℝ)) (s := (0.874404367461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601088672490 : ℝ) ≤ 0.678533917937 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601088672490 : ℝ)) (Q := (0.601088672490 : ℝ))
      (s := (0.799182337020 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774334832302 : ℝ)) (R := (0.774859696242 : ℝ)) (Q2 := (0.601088672490 : ℝ)) (T := (0.824198535623 : ℝ))
    (B := ((6804383463792617/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484006550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (67988114239017/100000000000000) := by
  have hk1 : kappa q ≤ 0.598427280166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484006550001 : ℝ)) (s := (0.875064374522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600298878516 : ℝ) ≤ 0.677975032348 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600298878516 : ℝ)) (Q := (0.600298878516 : ℝ))
      (s := (0.799775753854 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773825605706 : ℝ)) (R := (0.774350469646 : ℝ)) (Q2 := (0.600298878516 : ℝ)) (T := (0.823859033379 : ℝ))
    (B := ((67988114239017/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482815200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1698311377854149/2500000000000000) := by
  have hk1 : kappa q ≤ 0.597639445009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482815200001 : ℝ)) (s := (0.875722263420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599509614461 : ℝ) ≤ 0.677416783613 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599509614461 : ℝ)) (Q := (0.599509614461 : ℝ))
      (s := (0.800367554421 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773316386021 : ℝ)) (R := (0.773841249961 : ℝ)) (Q2 := (0.599509614461 : ℝ)) (T := (0.823519778278 : ℝ))
    (B := ((1698311377854149/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481623850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6787685716898793/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596852138620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481623850001 : ℝ)) (s := (0.876378038926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598720879782 : ℝ) ≤ 0.676859170591 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598720879782 : ℝ)) (Q := (0.598720879782 : ℝ))
      (s := (0.800957744275 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772807172909 : ℝ)) (R := (0.773332036849 : ℝ)) (Q2 := (0.598720879782 : ℝ)) (T := (0.823180769930 : ℝ))
    (B := ((6787685716898793/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480432500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782132030944337/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596065360454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480432500001 : ℝ)) (s := (0.877031705780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597932673933 : ℝ) ≤ 0.676302192142 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597932673933 : ℝ)) (Q := (0.597932673933 : ℝ))
      (s := (0.801546328944 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772297966030 : ℝ)) (R := (0.772822829970 : ℝ)) (Q2 := (0.597932673933 : ℝ)) (T := (0.822842007947 : ℝ))
    (B := ((6782132030944337/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479241150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3388292222091817/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595279109971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479241150001 : ℝ)) (s := (0.877683268695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597144996371 : ℝ) ≤ 0.675745847131 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597144996371 : ℝ)) (Q := (0.597144996371 : ℝ))
      (s := (0.802133313926 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771788765046 : ℝ)) (R := (0.772313628986 : ℝ)) (Q2 := (0.597144996371 : ℝ)) (T := (0.822503491943 : ℝ))
    (B := ((3388292222091817/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 13200 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478049800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771042947281251/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594493386633 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478049800001 : ℝ)) (s := (0.878332732351 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596357846557 : ℝ) ≤ 0.675190134426 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596357846557 : ℝ)) (Q := (0.596357846557 : ℝ))
      (s := (0.802718704685 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771279569620 : ℝ)) (R := (0.771804433560 : ℝ)) (Q2 := (0.596357846557 : ℝ)) (T := (0.822165221532 : ℝ))
    (B := ((6771042947281251/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S34
namespace BstLean.Part269.S34
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 13200 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.051470021449 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S34.wn_upper (by omega : 13200 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010394503939 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035118561495)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010394503939 + 2 * 0.737676 / 13200) := by gcongr
    _ ≤ (0.051470021449 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 13200 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 13200 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.891252930760 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (13200 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (114.891252930760 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 13200 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003118785860 + 0.003164686405 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003118785860 + 0.003164686405 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.891252930760 ≤ R)
    (hB : (X + 0.051470021449 + R + 0.008318556854) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008318556854 := by
    convert (BstLean.Part269.S34.finite_centre_upper (by omega : 13200 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (10511562637/125000000000)
  | 2 => (42507042147/500000000000)
  | 3 => (42965427813/500000000000)
  | 4 => (17368707313/200000000000)
  | 5 => (8775301899/100000000000)
  | 6 => (88660392791/1000000000000)
  | 7 => (5597936033/62500000000)
  | 8 => (22618587813/250000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003118785860 + 0.003164686405 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218030222685 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010756845688 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003118785860 + 0.003164686405 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.219606344794 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010869614542 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003118785860 + 0.003164686405 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221161787708 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.010982010930 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003118785860 + 0.003164686405 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.222696766348 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011094043017 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003118785860 + 0.003164686405 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224211490085 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011205718734 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003118785860 + 0.003164686405 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.225706161262 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011317045670 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003118785860 + 0.003164686405 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227180977102 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011428031206 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 13200 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003118785860 + 0.003164686405 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.228636128254 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011538682409 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 13200 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g) :
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

end BstLean.Part269.S34

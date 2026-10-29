import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S26
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 13000 ≤ n) : wn n ≤ 1.035390013080 := by
  have hnR : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (114.017542509913 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (114.017542509913 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035390013080 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 13000 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 13000 + 24 / (13000 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 13000 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008382572401 : ℝ) := by
  have hnR : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (114.017542509913 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (13000 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035390013080 * (81 / 1000 / 13000)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035390013080 * n *
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
        4 * (1 / 2.506628) * 1.035390013080 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035390013080 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035390013080 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 13000)) / 114.017542509913 := by gcongr
    _ ≤ (0.008382572401 : ℝ) := by norm_num

end BstLean.Part269.S26
namespace BstLean.Part269.S26
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 13000 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 13000 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 13000 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 13000 + 0.008382572401 / 114.017542509913) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 13000 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 13000 := by gcongr
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
  have hn : (114.017542509913 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S26.finite_centre_upper (by omega : 13000 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528086500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (438100793649353/625000000000000) := by
  have hk1 : kappa q ≤ 0.627954155981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528086500001 : ℝ)) (s := (0.849190584332 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629897721913 : ℝ) ≤ 0.699101376929 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629897721913 : ℝ)) (Q := (0.629897721913 : ℝ))
      (s := (0.776678092861 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792678226878 : ℝ)) (R := (0.793211165648 : ℝ)) (Q2 := (0.629897721913 : ℝ)) (T := (0.836596679463 : ℝ))
    (B := ((438100793649353/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526895150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3501906536385907/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627146345960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526895150001 : ℝ)) (s := (0.849930291792 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629088451581 : ℝ) ≤ 0.698518754998 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629088451581 : ℝ)) (Q := (0.629088451581 : ℝ))
      (s := (0.777333725042 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792168518275 : ℝ)) (R := (0.792701457045 : ℝ)) (Q2 := (0.629088451581 : ℝ)) (T := (0.836248002445 : ℝ))
    (B := ((3501906536385907/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525703800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (874752492459027/1250000000000000) := by
  have hk1 : kappa q ≤ 0.626339086996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525703800001 : ℝ)) (s := (0.850667687564 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628279732950 : ℝ) ≤ 0.697936813896 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628279732950 : ℝ)) (Q := (0.628279732950 : ℝ))
      (s := (0.777987517358 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791658829535 : ℝ)) (R := (0.792191768305 : ℝ)) (Q2 := (0.628279732950 : ℝ)) (T := (0.835899587688 : ℝ))
    (B := ((874752492459027/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524512450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (699223328825993/1000000000000000) := by
  have hk1 : kappa q ≤ 0.625532378429 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524512450001 : ℝ)) (s := (0.851402777653 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627471565364 : ℝ) ≤ 0.697355552333 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627471565364 : ℝ)) (Q := (0.627471565364 : ℝ))
      (s := (0.778639476690 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791149160282 : ℝ)) (R := (0.791682099052 : ℝ)) (Q2 := (0.627471565364 : ℝ)) (T := (0.835551434750 : ℝ))
    (B := ((699223328825993/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523321100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986453107746967/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624726219604 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523321100001 : ℝ)) (s := (0.852135568026 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626663948163 : ℝ) ≤ 0.696774969017 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626663948163 : ℝ)) (Q := (0.626663948163 : ℝ))
      (s := (0.779289609884 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790639510137 : ℝ)) (R := (0.791172448907 : ℝ)) (Q2 := (0.626663948163 : ℝ)) (T := (0.835203543181 : ℝ))
    (B := ((6986453107746967/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522129750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6980679387388001/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623920609872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522129750001 : ℝ)) (s := (0.852866064611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625856880697 : ℝ) ≤ 0.696195062664 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625856880697 : ℝ)) (Q := (0.625856880697 : ℝ))
      (s := (0.779937923738 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790129878727 : ℝ)) (R := (0.790662817497 : ℝ)) (Q2 := (0.625856880697 : ℝ)) (T := (0.834855912540 : ℝ))
    (B := ((6980679387388001/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520938400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6974912116480101/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623115548582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520938400001 : ℝ)) (s := (0.853594273297 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625050362316 : ℝ) ≤ 0.695615831993 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625050362316 : ℝ)) (Q := (0.625050362316 : ℝ))
      (s := (0.780584425011 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789620265677 : ℝ)) (R := (0.790153204447 : ℝ)) (Q2 := (0.625050362316 : ℝ)) (T := (0.834508542384 : ℝ))
    (B := ((6974912116480101/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519747050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (871143910545309/1250000000000000) := by
  have hk1 : kappa q ≤ 0.622311035089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519747050001 : ℝ)) (s := (0.854320199934 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624244392372 : ℝ) ≤ 0.695037275727 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624244392372 : ℝ)) (Q := (0.624244392372 : ℝ))
      (s := (0.781229120420 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789110670612 : ℝ)) (R := (0.789643609382 : ℝ)) (Q2 := (0.624244392372 : ℝ)) (T := (0.834161432272 : ℝ))
    (B := ((871143910545309/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518555700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3481698440208091/5000000000000000) := by
  have hk1 : kappa q ≤ 0.621507068752 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518555700001 : ℝ)) (s := (0.855043850336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623438970224 : ℝ) ≤ 0.694459392595 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623438970224 : ℝ)) (Q := (0.623438970224 : ℝ))
      (s := (0.781872016641 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788601093163 : ℝ)) (R := (0.789134031933 : ℝ)) (Q2 := (0.623438970224 : ℝ)) (T := (0.833814581766 : ℝ))
    (B := ((3481698440208091/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517364350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3478824447031957/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620703648931 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517364350001 : ℝ)) (s := (0.855765230276 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622634095231 : ℝ) ≤ 0.693882181328 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622634095231 : ℝ)) (Q := (0.622634095231 : ℝ))
      (s := (0.782513120310 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788091532956 : ℝ)) (R := (0.788624471726 : ℝ)) (Q2 := (0.622634095231 : ℝ)) (T := (0.833467990428 : ℝ))
    (B := ((3478824447031957/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516173000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3475953657384849/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619900774988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516173000001 : ℝ)) (s := (0.856484345491 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621829766752 : ℝ) ≤ 0.693305640656 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621829766752 : ℝ)) (Q := (0.621829766752 : ℝ))
      (s := (0.783152438023 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787581989620 : ℝ)) (R := (0.788114928390 : ℝ)) (Q2 := (0.621829766752 : ℝ)) (T := (0.833121657818 : ℝ))
    (B := ((3475953657384849/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514981650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473086066019331/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619098446292 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514981650001 : ℝ)) (s := (0.857201201681 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621025984156 : ℝ) ≤ 0.692729769324 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621025984156 : ℝ)) (Q := (0.621025984156 : ℝ))
      (s := (0.783789976335 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787072462787 : ℝ)) (R := (0.787605401557 : ℝ)) (Q2 := (0.621025984156 : ℝ)) (T := (0.832775583505 : ℝ))
    (B := ((3473086066019331/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513790300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (867555416927097/1250000000000000) := by
  have hk1 : kappa q ≤ 0.618296662211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513790300001 : ℝ)) (s := (0.857915804509 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620222746810 : ℝ) ≤ 0.692154566072 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620222746810 : ℝ)) (Q := (0.620222746810 : ℝ))
      (s := (0.784425741763 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786562952087 : ℝ)) (R := (0.787095890857 : ℝ)) (Q2 := (0.620222746810 : ℝ)) (T := (0.832429767054 : ℝ))
    (B := ((867555416927097/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512598950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6934720914490599/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617495422118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512598950001 : ℝ)) (s := (0.858628159600 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619420054087 : ℝ) ≤ 0.691580029649 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619420054087 : ℝ)) (Q := (0.619420054087 : ℝ))
      (s := (0.785059740781 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786053457154 : ℝ)) (R := (0.786586395924 : ℝ)) (Q2 := (0.619420054087 : ℝ)) (T := (0.832084208032 : ℝ))
    (B := ((6934720914490599/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511407600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3464502429443517/5000000000000000) := by
  have hk1 : kappa q ≤ 0.616694725391 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511407600001 : ℝ)) (s := (0.859338272546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618617905363 : ℝ) ≤ 0.691006158806 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618617905363 : ℝ)) (Q := (0.618617905363 : ℝ))
      (s := (0.785691979827 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785543977621 : ℝ)) (R := (0.786076916391 : ℝ)) (Q2 := (0.618617905363 : ℝ)) (T := (0.831738906009 : ℝ))
    (B := ((3464502429443517/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510216250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (173082378956827/250000000000000) := by
  have hk1 : kappa q ≤ 0.615894571407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510216250001 : ℝ)) (s := (0.860046148899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617816300013 : ℝ) ≤ 0.690432952299 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617816300013 : ℝ)) (Q := (0.617816300013 : ℝ))
      (s := (0.786322465302 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785034513122 : ℝ)) (R := (0.785567451892 : ℝ)) (Q2 := (0.617816300013 : ℝ)) (T := (0.831393860557 : ℝ))
    (B := ((173082378956827/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509024900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1383518360471117/2000000000000000) := by
  have hk1 : kappa q ≤ 0.615094959549 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509024900001 : ℝ)) (s := (0.860751794178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617015237420 : ℝ) ≤ 0.689860408887 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617015237420 : ℝ)) (Q := (0.617015237420 : ℝ))
      (s := (0.786951203565 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784525063293 : ℝ)) (R := (0.785058002063 : ℝ)) (Q2 := (0.617015237420 : ℝ)) (T := (0.831049071248 : ℝ))
    (B := ((1383518360471117/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507833550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1382378956176201/2000000000000000) := by
  have hk1 : kappa q ≤ 0.614295889201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507833550001 : ℝ)) (s := (0.861455213864 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616214716965 : ℝ) ≤ 0.689288527332 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616214716965 : ℝ)) (Q := (0.616214716965 : ℝ))
      (s := (0.787578200940 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784015627769 : ℝ)) (R := (0.784548566539 : ℝ)) (Q2 := (0.616214716965 : ℝ)) (T := (0.830704537654 : ℝ))
    (B := ((1382378956176201/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506642200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1381240816727033/2000000000000000) := by
  have hk1 : kappa q ≤ 0.613497359753 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506642200001 : ℝ)) (s := (0.862156413407 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615414738041 : ℝ) ≤ 0.688717306407 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615414738041 : ℝ)) (Q := (0.615414738041 : ℝ))
      (s := (0.788203463709 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783506206190 : ℝ)) (R := (0.784039144960 : ℝ)) (Q2 := (0.615414738041 : ℝ)) (T := (0.830360259355 : ℝ))
    (B := ((1381240816727033/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505450850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900519700443019/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612699370595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505450850001 : ℝ)) (s := (0.862855398218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614615300033 : ℝ) ≤ 0.688146744879 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614615300033 : ℝ)) (Q := (0.614615300033 : ℝ))
      (s := (0.788826998122 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782996798193 : ℝ)) (R := (0.783529736963 : ℝ)) (Q2 := (0.614615300033 : ℝ)) (T := (0.830016235923 : ℝ))
    (B := ((6900519700443019/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504259500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6894841621168411/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611901921122 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504259500001 : ℝ)) (s := (0.863552173675 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613816402337 : ℝ) ≤ 0.687576841528 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613816402337 : ℝ)) (Q := (0.613816402337 : ℝ))
      (s := (0.789448810388 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782487403418 : ℝ)) (R := (0.783020342188 : ℝ)) (Q2 := (0.613816402337 : ℝ)) (T := (0.829672466941 : ℝ))
    (B := ((6894841621168411/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503068150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889169835713847/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611105010733 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503068150001 : ℝ)) (s := (0.864246745123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613018044350 : ℝ) ≤ 0.687007595133 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613018044350 : ℝ)) (Q := (0.613018044350 : ℝ))
      (s := (0.790068906680 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781978021506 : ℝ)) (R := (0.782510960276 : ℝ)) (Q2 := (0.613018044350 : ℝ)) (T := (0.829328951988 : ℝ))
    (B := ((6889169835713847/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501876800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883504334020257/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610308638826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501876800001 : ℝ)) (s := (0.864939117870 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612220225469 : ℝ) ≤ 0.686439004477 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612220225469 : ℝ)) (Q := (0.612220225469 : ℝ))
      (s := (0.790687293136 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781468652098 : ℝ)) (R := (0.782001590868 : ℝ)) (Q2 := (0.612220225469 : ℝ)) (T := (0.828985690644 : ℝ))
    (B := ((6883504334020257/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500685450001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (429865319129173/625000000000000) := by
  have hk1 : kappa q ≤ 0.609512804807 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500685450001 : ℝ)) (s := (0.865629297193 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611422945099 : ℝ) ≤ 0.685871068352 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611422945099 : ℝ)) (Q := (0.611422945099 : ℝ))
      (s := (0.791303975857 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780959294837 : ℝ)) (R := (0.781492233607 : ℝ)) (Q2 := (0.611422945099 : ℝ)) (T := (0.828642682495 : ℝ))
    (B := ((429865319129173/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499494100001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (859024017733809/1250000000000000) := by
  have hk1 : kappa q ≤ 0.608717508081 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499494100001 : ℝ)) (s := (0.866317288333 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610626202645 : ℝ) ≤ 0.685303785550 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610626202645 : ℝ)) (Q := (0.610626202645 : ℝ))
      (s := (0.791918960907 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780449949367 : ℝ)) (R := (0.780982888137 : ℝ)) (Q2 := (0.610626202645 : ℝ)) (T := (0.828299927126 : ℝ))
    (B := ((859024017733809/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498302750001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1373309086297241/2000000000000000) := by
  have hk1 : kappa q ≤ 0.607922748060 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498302750001 : ℝ)) (s := (0.867003096501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609829997516 : ℝ) ≤ 0.684737154868 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609829997516 : ℝ)) (Q := (0.609829997516 : ℝ))
      (s := (0.792532254316 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779940615333 : ℝ)) (R := (0.780473554103 : ℝ)) (Q2 := (0.609829997516 : ℝ)) (T := (0.827957424123 : ℝ))
    (B := ((1373309086297241/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497111400001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6860904965006317/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607128524156 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497111400001 : ℝ)) (s := (0.867686726872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609034329124 : ℝ) ≤ 0.684171175107 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609034329124 : ℝ)) (Q := (0.609034329124 : ℝ))
      (s := (0.793143862076 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779431292380 : ℝ)) (R := (0.779964231150 : ℝ)) (Q2 := (0.609034329124 : ℝ)) (T := (0.827615173074 : ℝ))
    (B := ((6860904965006317/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495920050001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855270732560451/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606334835785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495920050001 : ℝ)) (s := (0.868368184590 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608239196884 : ℝ) ≤ 0.683605845074 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608239196884 : ℝ)) (Q := (0.608239196884 : ℝ))
      (s := (0.793753790148 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778921980156 : ℝ)) (R := (0.779454918926 : ℝ)) (Q2 := (0.608239196884 : ℝ)) (T := (0.827273173571 : ℝ))
    (B := ((6855270732560451/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494728700001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (273985708972613/400000000000000) := by
  have hk1 : kappa q ≤ 0.605541682366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494728700001 : ℝ)) (s := (0.869047474765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607444600214 : ℝ) ≤ 0.683041163577 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607444600214 : ℝ)) (Q := (0.607444600214 : ℝ))
      (s := (0.794362044456 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778412678308 : ℝ)) (R := (0.778945617078 : ℝ)) (Q2 := (0.607444600214 : ℝ)) (T := (0.826931425203 : ℝ))
    (B := ((273985708972613/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493537350001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844020930474509/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604749063323 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493537350001 : ℝ)) (s := (0.869724602478 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606650538538 : ℝ) ≤ 0.682477129434 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606650538538 : ℝ)) (Q := (0.606650538538 : ℝ))
      (s := (0.794968630886 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777903386487 : ℝ)) (R := (0.778436325257 : ℝ)) (Q2 := (0.606650538538 : ℝ)) (T := (0.826589927567 : ℝ))
    (B := ((6844020930474509/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492346000001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683840534127821/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603956978079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492346000001 : ℝ)) (s := (0.870399572773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605857011276 : ℝ) ≤ 0.681913741460 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605857011276 : ℝ)) (Q := (0.605857011276 : ℝ))
      (s := (0.795573555297 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777394104341 : ℝ)) (R := (0.777927043111 : ℝ)) (Q2 := (0.605857011276 : ℝ)) (T := (0.826248680255 : ℝ))
    (B := ((683840534127821/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491154650001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6832795947003057/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603165426065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491154650001 : ℝ)) (s := (0.871072390668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605064017860 : ℝ) ≤ 0.681350998480 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605064017860 : ℝ)) (Q := (0.605064017860 : ℝ))
      (s := (0.796176823508 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776884831523 : ℝ)) (R := (0.777417770293 : ℝ)) (Q2 := (0.605064017860 : ℝ)) (T := (0.825907682865 : ℝ))
    (B := ((6832795947003057/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489963300001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413596368980943/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602374406710 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489963300001 : ℝ)) (s := (0.871743061144 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604271557715 : ℝ) ≤ 0.680788899317 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604271557715 : ℝ)) (Q := (0.604271557715 : ℝ))
      (s := (0.796778441311 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776375567683 : ℝ)) (R := (0.776908506453 : ℝ)) (Q2 := (0.604271557715 : ℝ)) (T := (0.825566934994 : ℝ))
    (B := ((3413596368980943/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488771950001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (682159570450353/1000000000000000) := by
  have hk1 : kappa q ≤ 0.601583919451 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488771950001 : ℝ)) (s := (0.872411589156 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603479630280 : ℝ) ≤ 0.680227442807 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603479630280 : ℝ)) (Q := (0.603479630280 : ℝ))
      (s := (0.797378414454 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775866312477 : ℝ)) (R := (0.776399251247 : ℝ)) (Q2 := (0.603479630280 : ℝ)) (T := (0.825226436245 : ℝ))
    (B := ((682159570450353/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487580600001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3408002418506303/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600793963725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487580600001 : ℝ)) (s := (0.873077979624 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602688234990 : ℝ) ≤ 0.679666627783 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602688234990 : ℝ)) (Q := (0.602688234990 : ℝ))
      (s := (0.797976748662 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775357065558 : ℝ)) (R := (0.775890004328 : ℝ)) (Q2 := (0.602688234990 : ℝ)) (T := (0.824886186218 : ℝ))
    (B := ((3408002418506303/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486389250001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810420125909313/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600004538972 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486389250001 : ℝ)) (s := (0.873742237439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601897371283 : ℝ) ≤ 0.679106453084 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601897371283 : ℝ)) (Q := (0.601897371283 : ℝ))
      (s := (0.798573449623 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774847826581 : ℝ)) (R := (0.775380765351 : ℝ)) (Q2 := (0.601897371283 : ℝ)) (T := (0.824546184516 : ℝ))
    (B := ((6810420125909313/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485197900001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804841561649217/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599215644636 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485197900001 : ℝ)) (s := (0.874404367461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601107038603 : ℝ) ≤ 0.678546917555 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601107038603 : ℝ)) (Q := (0.601107038603 : ℝ))
      (s := (0.799168522993 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774338595203 : ℝ)) (R := (0.774871533973 : ℝ)) (Q2 := (0.601107038603 : ℝ)) (T := (0.824206430744 : ℝ))
    (B := ((6804841561649217/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484006550001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399634567361527/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598427280166 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484006550001 : ℝ)) (s := (0.875064374522 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600317236398 : ℝ) ≤ 0.677988020045 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600317236398 : ℝ)) (Q := (0.600317236398 : ℝ))
      (s := (0.799761974393 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773829371083 : ℝ)) (R := (0.774362309853 : ℝ)) (Q2 := (0.600317236398 : ℝ)) (T := (0.823866924511 : ℝ))
    (B := ((3399634567361527/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482815200001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (169842570891413/250000000000000) := by
  have hk1 : kappa q ≤ 0.597639445009 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482815200001 : ℝ)) (s := (0.875722263420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599527964114 : ℝ) ≤ 0.677429759405 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599527964114 : ℝ)) (Q := (0.599527964114 : ℝ))
      (s := (0.800353809416 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773320153878 : ℝ)) (R := (0.773853092648 : ℝ)) (Q2 := (0.599527964114 : ℝ)) (T := (0.823527665424 : ℝ))
    (B := ((169842570891413/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481623850001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1697035663752519/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596852138620 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481623850001 : ℝ)) (s := (0.876378038926 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598739221205 : ℝ) ≤ 0.676872134491 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598739221205 : ℝ)) (Q := (0.598739221205 : ℝ))
      (s := (0.800944033620 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772810943249 : ℝ)) (R := (0.773343882019 : ℝ)) (Q2 := (0.598739221205 : ℝ)) (T := (0.823188653093 : ℝ))
    (B := ((1697035663752519/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480432500001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (847823572922343/1250000000000000) := by
  have hk1 : kappa q ≤ 0.596065360454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480432500001 : ℝ)) (s := (0.877031705780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597951007126 : ℝ) ≤ 0.676315144166 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597951007126 : ℝ)) (Q := (0.597951007126 : ℝ))
      (s := (0.801532652534 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772301738856 : ℝ)) (R := (0.772834677626 : ℝ)) (Q2 := (0.597951007126 : ℝ)) (T := (0.822849887131 : ℝ))
    (B := ((847823572922343/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479241150001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (677704061139191/1000000000000000) := by
  have hk1 : kappa q ≤ 0.595279109971 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479241150001 : ℝ)) (s := (0.877683268695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597163321333 : ℝ) ≤ 0.675758787293 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597163321333 : ℝ)) (Q := (0.597163321333 : ℝ))
      (s := (0.802119671655 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771792540361 : ℝ)) (R := (0.772325479131 : ℝ)) (Q2 := (0.597163321333 : ℝ)) (T := (0.822511367150 : ℝ))
    (B := ((677704061139191/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 13000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478049800001/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771498729713127/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594493386633 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478049800001 : ℝ)) (s := (0.878332732351 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596376163289 : ℝ) ≤ 0.675203062742 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596376163289 : ℝ)) (Q := (0.596376163289 : ℝ))
      (s := (0.802705096447 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771283347427 : ℝ)) (R := (0.771816286197 : ℝ)) (Q2 := (0.596376163289 : ℝ)) (T := (0.822173092768 : ℝ))
    (B := ((6771498729713127/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S26
namespace BstLean.Part269.S26
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 13000 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.051868661545 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S26.wn_upper (by omega : 13000 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010474156475 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035390013080)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010474156475 + 2 * 0.737676 / 13000) := by gcongr
    _ ≤ (0.051868661545 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 13000 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 13000 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.017542509913 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (114.017542509913 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 13000 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003229261452 + 0.003215050469 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003229261452 + 0.003215050469 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.017542509913 ≤ R)
    (hB : (X + 0.051868661545 + R + 0.008382572401) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008382572401 := by
    convert (BstLean.Part269.S26.finite_centre_upper (by omega : 13000 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (84597498963/1000000000000)
  | 2 => (42762675469/500000000000)
  | 3 => (8644928767/100000000000)
  | 4 => (87370244367/1000000000000)
  | 5 => (44144683167/500000000000)
  | 6 => (22302010483/250000000000)
  | 7 => (18025587793/200000000000)
  | 8 => (91051044601/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003229261452 + 0.003215050469 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218338145931 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010839274829 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003229261452 + 0.003215050469 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.219912885229 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010952907826 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003229261452 + 0.003215050469 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221466993499 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011066165501 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003229261452 + 0.003215050469 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223000683992 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011179056084 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003229261452 + 0.003215050469 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224514164490 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011291587566 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003229261452 + 0.003215050469 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226007635831 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011403767595 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003229261452 + 0.003215050469 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227481293804 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011515603607 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 13000 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003229261452 + 0.003215050469 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.228935327697 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011627102725 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 13000 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g) :
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

end BstLean.Part269.S26

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S12
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12650 ≤ n) : wn n ≤ 1.035880543492 := by
  have hnR : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.472218792019 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.472218792019 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035880543492 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12650 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12650 + 24 / (12650 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12650 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008498241865 : ℝ) := by
  have hnR : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.472218792019 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12650 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035880543492 * (81 / 1000 / 12650)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035880543492 * n *
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
        4 * (1 / 2.506628) * 1.035880543492 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035880543492 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035880543492 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12650)) / 112.472218792019 := by gcongr
    _ ≤ (0.008498241865 : ℝ) := by norm_num

end BstLean.Part269.S12
namespace BstLean.Part269.S12
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12650 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12650 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12650 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12650 + 0.008498241865 / 112.472218792019) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12650 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12650 := by gcongr
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
  have hn : (112.472218792019 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S12.finite_centre_upper (by omega : 12650 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528055170177/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (701032263676139/1000000000000000) := by
  have hk1 : kappa q ≤ 0.627932905334 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528055170177 : ℝ)) (s := (0.849210066621 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629910512517 : ℝ) ≤ 0.699110587611 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629910512517 : ℝ)) (Q := (0.629910512517 : ℝ))
      (s := (0.776667719312 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792671534907 : ℝ)) (R := (0.793219219018 : ℝ)) (Q2 := (0.629910512517 : ℝ)) (T := (0.836602190539 : ℝ))
    (B := ((701032263676139/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263430343597/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004507199458003/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627122986220 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526860687194 : ℝ)) (s := (0.849951655267 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629099114186 : ℝ) ≤ 0.698526429533 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629099114186 : ℝ)) (Q := (0.629099114186 : ℝ))
      (s := (0.777325095781 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792160490771 : ℝ)) (R := (0.792708174882 : ℝ)) (Q2 := (0.629099114186 : ℝ)) (T := (0.836252596306 : ℝ))
    (B := ((7004507199458003/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131416551053/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1749674572364447/2500000000000000) := by
  have hk1 : kappa q ≤ 0.626313621045 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525666204212 : ℝ)) (s := (0.850690920223 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628288270444 : ℝ) ≤ 0.697942955862 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628288270444 : ℝ)) (Q := (0.628288270444 : ℝ))
      (s := (0.777980622653 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791649466597 : ℝ)) (R := (0.792197150708 : ℝ)) (Q2 := (0.628288270444 : ℝ)) (T := (0.835903265712 : ℝ))
    (B := ((1749674572364447/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52447172123/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1398579179168637/2000000000000000) := by
  have hk1 : kappa q ≤ 0.625504809145 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524471721230 : ℝ)) (s := (0.851427867544 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477980625 : ℝ) ≤ 0.697360165293 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477980625 : ℝ)) (Q := (0.627477980625 : ℝ))
      (s := (0.778634306868 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791138462004 : ℝ)) (R := (0.791686146115 : ℝ)) (Q2 := (0.627477980625 : ℝ)) (T := (0.835554198303 : ℝ))
    (B := ((1398579179168637/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523277238247/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987100007740021/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624696549860 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523277238247 : ℝ)) (s := (0.852162503243 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668244069 : ℝ) ≤ 0.696778056530 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668244069 : ℝ)) (Q := (0.626668244069 : ℝ))
      (s := (0.779286155322 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790627476614 : ℝ)) (R := (0.791175160725 : ℝ)) (Q2 := (0.626668244069 : ℝ)) (T := (0.835205393634 : ℝ))
    (B := ((6987100007740021/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (104416551053/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (174532765357931/250000000000000) := by
  have hk1 : kappa q ≤ 0.623888842535 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522082755265 : ℝ)) (s := (0.852894833292 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859060121 : ℝ) ≤ 0.696196628277 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859060121 : ℝ)) (Q := (0.625859060121 : ℝ))
      (s := (0.779936174866 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790116510049 : ℝ)) (R := (0.790664194160 : ℝ)) (Q2 := (0.625859060121 : ℝ)) (T := (0.834856851257 : ℝ))
    (B := ((174532765357931/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (260444136141/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975527704786633/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623081686515 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520888272282 : ℝ)) (s := (0.853624863626 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625050428124 : ℝ) ≤ 0.695615879244 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625050428124 : ℝ)) (Q := (0.625050428124 : ℝ))
      (s := (0.780584372315 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789605561931 : ℝ)) (R := (0.790153246042 : ℝ)) (Q2 := (0.625050428124 : ℝ)) (T := (0.834508570727 : ℝ))
    (B := ((6975527704786633/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5196937893/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969751268402571/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622275081151 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519693789300 : ℝ)) (s := (0.854352600139 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624242347426 : ℝ) ≤ 0.695035808143 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624242347426 : ℝ)) (Q := (0.624242347426 : ℝ))
      (s := (0.781230754439 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789094631884 : ℝ)) (R := (0.789642315995 : ℝ)) (Q2 := (0.624242347426 : ℝ)) (T := (0.834160551598 : ℝ))
    (B := ((6969751268402571/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259249653159/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3481990647230867/5000000000000000) := by
  have hk1 : kappa q ≤ 0.621469025795 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518499306318 : ℝ)) (s := (0.855078048688 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623434817381 : ℝ) ≤ 0.694456413692 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623434817381 : ℝ)) (Q := (0.623434817381 : ℝ))
      (s := (0.781875327963 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788583719533 : ℝ)) (R := (0.789131403644 : ℝ)) (Q2 := (0.623434817381 : ℝ)) (T := (0.833812793429 : ℝ))
    (B := ((3481990647230867/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103460964667/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958217772302851/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620663519801 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517304823335 : ℝ)) (s := (0.855801215093 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622627837339 : ℝ) ≤ 0.693877694611 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622627837339 : ℝ)) (Q := (0.622627837339 : ℝ))
      (s := (0.782518099581 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788072824502 : ℝ)) (R := (0.788620508613 : ℝ)) (Q2 := (0.622627837339 : ℝ)) (T := (0.833465295777 : ℝ))
    (B := ((6958217772302851/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516110340353/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952460691306441/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619858562531 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516110340353 : ℝ)) (s := (0.856522105133 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621821406663 : ℝ) ≤ 0.693299649627 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621821406663 : ℝ)) (Q := (0.621821406663 : ℝ))
      (s := (0.783159075933 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787561946420 : ℝ)) (R := (0.788109630531 : ℝ)) (Q2 := (0.621821406663 : ℝ)) (T := (0.833118058203 : ℝ))
    (B := ((6952460691306441/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514915857371/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1736677510223637/2500000000000000) := by
  have hk1 : kappa q ≤ 0.619054153344 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514915857371 : ℝ)) (s := (0.857240724551 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621015524709 : ℝ) ≤ 0.692722277467 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621015524709 : ℝ)) (Q := (0.621015524709 : ℝ))
      (s := (0.783798263631 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787051084912 : ℝ)) (R := (0.787598769023 : ℝ)) (Q2 := (0.621015524709 : ℝ)) (T := (0.832771080269 : ℝ))
    (B := ((1736677510223637/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128430343597/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (694096581053049/1000000000000000) := by
  have hk1 : kappa q ≤ 0.618250291606 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513721374388 : ℝ)) (s := (0.857957079053 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620210190844 : ℝ) ≤ 0.692145576867 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620210190844 : ℝ)) (Q := (0.620210190844 : ℝ))
      (s := (0.784435669239 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786540239609 : ℝ)) (R := (0.787087923720 : ℝ)) (Q2 := (0.620210190844 : ℝ)) (T := (0.832424361537 : ℝ))
    (B := ((694096581053049/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256263445703/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (34676139948593/50000000000000) := by
  have hk1 : kappa q ≤ 0.617446976685 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512526891406 : ℝ)) (s := (0.858671174307 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619405404433 : ℝ) ≤ 0.691569546562 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619405404433 : ℝ)) (Q := (0.619405404433 : ℝ))
      (s := (0.785071299284 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786029410139 : ℝ)) (R := (0.786577094250 : ℝ)) (Q2 := (0.619405404433 : ℝ)) (T := (0.832077901571 : ℝ))
    (B := ((34676139948593/50000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511332408423/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929496568003979/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616644207953 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511332408423 : ℝ)) (s := (0.859383015946 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618601164847 : ℝ) ≤ 0.690994185296 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618601164847 : ℝ)) (Q := (0.618601164847 : ℝ))
      (s := (0.785705160255 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785518596133 : ℝ)) (R := (0.786066280244 : ℝ)) (Q2 := (0.618601164847 : ℝ)) (T := (0.831731699939 : ℝ))
    (B := ((6929496568003979/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510137925441/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (86547144187153/125000000000000) := by
  have hk1 : kappa q ≤ 0.615841984783 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510137925441 : ℝ)) (s := (0.860092609565 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617797471459 : ℝ) ≤ 0.690419491814 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617797471459 : ℝ)) (Q := (0.617797471459 : ℝ))
      (s := (0.786337258598 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785007797223 : ℝ)) (R := (0.785555481334 : ℝ)) (Q2 := (0.617797471459 : ℝ)) (T := (0.831385756208 : ℝ))
    (B := ((86547144187153/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508943442459/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1383610576049853/2000000000000000) := by
  have hk1 : kappa q ≤ 0.615040306554 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508943442459 : ℝ)) (s := (0.860799960722 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616994323646 : ℝ) ≤ 0.689845464867 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616994323646 : ℝ)) (Q := (0.616994323646 : ℝ))
      (s := (0.786967600724 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784497013042 : ℝ)) (R := (0.785044697153 : ℝ)) (Q2 := (0.616994323646 : ℝ)) (T := (0.831040069948 : ℝ))
    (B := ((1383610576049853/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126937239869/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1728085148375239/2500000000000000) := by
  have hk1 : kappa q ≤ 0.614239172644 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507748959476 : ℝ)) (s := (0.861505074943 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616191720785 : ℝ) ≤ 0.689272103206 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616191720785 : ℝ)) (Q := (0.616191720785 : ℝ))
      (s := (0.787596193006 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783986243222 : ℝ)) (R := (0.784533927333 : ℝ)) (Q2 := (0.616191720785 : ℝ)) (T := (0.830694640727 : ℝ))
    (B := ((1728085148375239/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253277238247/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906634664432993/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613438582440 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506554476494 : ℝ)) (s := (0.862207957714 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615389662264 : ℝ) ≤ 0.688699405595 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615389662264 : ℝ)) (Q := (0.615389662264 : ℝ))
      (s := (0.788223041771 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783475487401 : ℝ)) (R := (0.784023171512 : ℝ)) (Q2 := (0.615389662264 : ℝ)) (T := (0.830349468120 : ℝ))
    (B := ((6906634664432993/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63169999189/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900935082790593/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612638535326 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505359993512 : ℝ)) (s := (0.862908614488 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614588147462 : ℝ) ≤ 0.688127370792 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614588147462 : ℝ)) (Q := (0.614588147462 : ℝ))
      (s := (0.788848153322 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782964745211 : ℝ)) (R := (0.783512429322 : ℝ)) (Q2 := (0.614588147462 : ℝ)) (T := (0.830004551700 : ℝ))
    (B := ((6900935082790593/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504165510529/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895241838358269/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611839030693 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504165510529 : ℝ)) (s := (0.863607050686 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613787175773 : ℝ) ≤ 0.687555997567 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613787175773 : ℝ)) (Q := (0.613787175773 : ℝ))
      (s := (0.789471533912 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782454016292 : ℝ)) (R := (0.783001700403 : ℝ)) (Q2 := (0.613787175773 : ℝ)) (T := (0.829659891044 : ℝ))
    (B := ((6895241838358269/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502971027547/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444777460479797/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611040067935 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502971027547 : ℝ)) (s := (0.864303271687 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612986746586 : ℝ) ≤ 0.686985284689 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612986746586 : ℝ)) (Q := (0.612986746586 : ℝ))
      (s := (0.790093189764 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781943300280 : ℝ)) (R := (0.782490984391 : ℝ)) (Q2 := (0.612986746586 : ℝ)) (T := (0.829315485727 : ℝ))
    (B := ((3444777460479797/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125444136141/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1720968580114241/2500000000000000) := by
  have hk1 : kappa q ≤ 0.610241646446 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501776544564 : ℝ)) (s := (0.864997282843 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612186859296 : ℝ) ≤ 0.686415230933 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612186859296 : ℝ)) (Q := (0.612186859296 : ℝ))
      (s := (0.790713127061 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781432596814 : ℝ)) (R := (0.781980280925 : ℝ)) (Q2 := (0.612186859296 : ℝ)) (T := (0.828971335327 : ℝ))
    (B := ((1720968580114241/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250291030791/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (859775003343921/1250000000000000) := by
  have hk1 : kappa q ≤ 0.609443765628 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500582061582 : ℝ)) (s := (0.865689089468 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611387513304 : ℝ) ≤ 0.685845835082 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611387513304 : ℝ)) (Q := (0.611387513304 : ℝ))
      (s := (0.791331351949 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780921905536 : ℝ)) (R := (0.781469589647 : ℝ)) (Q2 := (0.611387513304 : ℝ)) (T := (0.828627439428 : ℝ))
    (B := ((859775003343921/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2496937893/5000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (137450640595643/200000000000000) := by
  have hk1 : kappa q ≤ 0.608646424882 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499387578600 : ℝ)) (s := (0.866378696842 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610588708010 : ℝ) ≤ 0.685277095917 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610588708010 : ℝ)) (Q := (0.610588708010 : ℝ))
      (s := (0.791947870539 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780411226085 : ℝ)) (R := (0.780958910196 : ℝ)) (Q2 := (0.610588708010 : ℝ)) (T := (0.828283797610 : ℝ))
    (B := ((137450640595643/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498193095617/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866870319526789/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607849623612 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498193095617 : ℝ)) (s := (0.867066110213 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609790442816 : ℝ) ≤ 0.684709012225 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609790442816 : ℝ)) (Q := (0.609790442816 : ℝ))
      (s := (0.792562688909 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779900558103 : ℝ)) (R := (0.780448242214 : ℝ)) (Q2 := (0.609790442816 : ℝ)) (T := (0.827940409456 : ℝ))
    (B := ((6866870319526789/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99399722527/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861214886000663/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607053361230 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496998612635 : ℝ)) (s := (0.867751334796 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608992717133 : ℝ) ≤ 0.684141582802 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608992717133 : ℝ)) (Q := (0.608992717133 : ℝ))
      (s := (0.793175813096 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779389901235 : ℝ)) (R := (0.779937585346 : ℝ)) (Q2 := (0.608992717133 : ℝ)) (T := (0.827597274552 : ℝ))
    (B := ((6861214886000663/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123951032413/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1713891429814207/2500000000000000) := by
  have hk1 : kappa q ≤ 0.606257637146 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495804129652 : ℝ)) (s := (0.868434375771 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608195530373 : ℝ) ≤ 0.683574806444 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608195530373 : ℝ)) (Q := (0.608195530373 : ℝ))
      (s := (0.793787249101 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778879255125 : ℝ)) (R := (0.779426939236 : ℝ)) (Q2 := (0.608195530373 : ℝ)) (T := (0.827254392487 : ℝ))
    (B := ((1713891429814207/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49460964667/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1369984561877159/2000000000000000) := by
  have hk1 : kappa q ≤ 0.605462450775 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494609646670 : ℝ)) (s := (0.869115238287 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607398881945 : ℝ) ≤ 0.683008681949 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607398881945 : ℝ)) (Q := (0.607398881945 : ℝ))
      (s := (0.794397002898 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778368619417 : ℝ)) (R := (0.778916303528 : ℝ)) (Q2 := (0.607398881945 : ℝ)) (T := (0.826911762846 : ℝ))
    (B := ((1369984561877159/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61676895461/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844286146515303/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604667801535 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493415163688 : ℝ)) (s := (0.869793927458 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606602771269 : ℝ) ≤ 0.682443208124 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606602771269 : ℝ)) (Q := (0.606602771269 : ℝ))
      (s := (0.795005080417 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777857993758 : ℝ)) (R := (0.778405677869 : ℝ)) (Q2 := (0.606602771269 : ℝ)) (T := (0.826569385221 : ℝ))
    (B := ((6844286146515303/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (98444136141/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838655720810107/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603873688847 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492220680705 : ℝ)) (s := (0.870470448371 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605807197764 : ℝ) ≤ 0.681878383778 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605807197764 : ℝ)) (Q := (0.605807197764 : ℝ))
      (s := (0.795611487560 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777347377795 : ℝ)) (R := (0.777895061906 : ℝ)) (Q2 := (0.605807197764 : ℝ)) (T := (0.826227259205 : ℝ))
    (B := ((6838655720810107/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491026197723/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (854128940308969/1250000000000000) := by
  have hk1 : kappa q ≤ 0.603080112137 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491026197723 : ℝ)) (s := (0.871144806074 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605012160856 : ℝ) ≤ 0.681314207727 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605012160856 : ℝ)) (Q := (0.605012160856 : ℝ))
      (s := (0.796216230189 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776836771178 : ℝ)) (R := (0.777384455289 : ℝ)) (Q2 := (0.605012160856 : ℝ)) (T := (0.825885384391 : ℝ))
    (B := ((854128940308969/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489831714741/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3413706770869181/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602287070830 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489831714741 : ℝ)) (s := (0.871817005589 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604217659968 : ℝ) ≤ 0.680750678786 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604217659968 : ℝ)) (Q := (0.604217659968 : ℝ))
      (s := (0.796819314138 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776326173556 : ℝ)) (R := (0.776873857667 : ℝ)) (Q2 := (0.604217659968 : ℝ)) (T := (0.825543760373 : ℝ))
    (B := ((3413706770869181/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244318615879/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852725221110553/1250000000000000) := by
  have hk1 : kappa q ≤ 0.601494564358 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488637231758 : ℝ)) (s := (0.872487051904 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603423694531 : ℝ) ≤ 0.680187795779 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603423694531 : ℝ)) (Q := (0.603423694531 : ℝ))
      (s := (0.797420745203 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775815584579 : ℝ)) (R := (0.776363268690 : ℝ)) (Q2 := (0.603423694531 : ℝ)) (T := (0.825202386751 : ℝ))
    (B := ((852725221110553/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60930343597/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (213006131069393/312500000000000) := by
  have hk1 : kappa q ≤ 0.600702592155 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487442748776 : ℝ)) (s := (0.873154949975 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602630263978 : ℝ) ≤ 0.679625557532 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602630263978 : ℝ)) (Q := (0.602630263978 : ℝ))
      (s := (0.798020529146 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775305003900 : ℝ)) (R := (0.775852688011 : ℝ)) (Q2 := (0.602630263978 : ℝ)) (T := (0.824861263121 : ℝ))
    (B := ((213006131069393/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486248265793/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1362119361618679/2000000000000000) := by
  have hk1 : kappa q ≤ 0.599911153656 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486248265793 : ℝ)) (s := (0.873820704730 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601837367744 : ℝ) ≤ 0.679063962877 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601837367744 : ℝ)) (Q := (0.601837367744 : ℝ))
      (s := (0.798618671700 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774794431171 : ℝ)) (R := (0.775342115282 : ℝ)) (Q2 := (0.601837367744 : ℝ)) (T := (0.824520389085 : ℝ))
    (B := ((1362119361618679/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485053782811/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1701250900221297/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599120248303 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485053782811 : ℝ)) (s := (0.874484321061 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601045005268 : ℝ) ≤ 0.678503010647 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601045005268 : ℝ)) (Q := (0.601045005268 : ℝ))
      (s := (0.799215178562 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774283866047 : ℝ)) (R := (0.774831550158 : ℝ)) (Q2 := (0.601045005268 : ℝ)) (T := (0.824179764245 : ℝ))
    (B := ((1701250900221297/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483859299829/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3399708281506893/5000000000000000) := by
  have hk1 : kappa q ≤ 0.598329875538 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483859299829 : ℝ)) (s := (0.875145803835 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600253175994 : ℝ) ≤ 0.677942699685 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600253175994 : ℝ)) (Q := (0.600253175994 : ℝ))
      (s := (0.799810055394 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773773308183 : ℝ)) (R := (0.774320992294 : ℝ)) (Q2 := (0.600253175994 : ℝ)) (T := (0.823839388206 : ℝ))
    (B := ((3399708281506893/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241332408423/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (424614730308271/625000000000000) := by
  have hk1 : kappa q ≤ 0.597540034806 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482664816846 : ℝ)) (s := (0.875805157886 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599461879362 : ℝ) ≤ 0.677383028830 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599461879362 : ℝ)) (Q := (0.599461879362 : ℝ))
      (s := (0.800403307835 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773262757233 : ℝ)) (R := (0.773810441344 : ℝ)) (Q2 := (0.599461879362 : ℝ)) (T := (0.823499260571 : ℝ))
    (B := ((424614730308271/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60183791733/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788260886312617/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596750725558 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481470333864 : ℝ)) (s := (0.876462388018 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598671114825 : ℝ) ≤ 0.676823996934 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598671114825 : ℝ)) (Q := (0.598671114825 : ℝ))
      (s := (0.800994941479 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772752212857 : ℝ)) (R := (0.773299896968 : ℝ)) (Q2 := (0.598671114825 : ℝ)) (T := (0.823159380950 : ℝ))
    (B := ((6788260886312617/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240137925441/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (423918194507009/625000000000000) := by
  have hk1 : kappa q ≤ 0.595961947244 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480275850882 : ℝ)) (s := (0.877117499005 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597880881832 : ℝ) ≤ 0.676265602847 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597880881832 : ℝ)) (Q := (0.597880881832 : ℝ))
      (s := (0.801584961898 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772241674712 : ℝ)) (R := (0.772789358823 : ℝ)) (Q2 := (0.597880881832 : ℝ)) (T := (0.822819748951 : ℝ))
    (B := ((423918194507009/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479081367899/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777127471876901/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595173699321 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479081367899 : ℝ)) (s := (0.877770495593 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597091179838 : ℝ) ≤ 0.675707845428 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597091179838 : ℝ)) (Q := (0.597091179838 : ℝ))
      (s := (0.802173374627 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771731142458 : ℝ)) (R := (0.772278826569 : ℝ)) (Q2 := (0.597091179838 : ℝ)) (T := (0.822480364185 : ℝ))
    (B := ((6777127471876901/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12650 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477886884917/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3385784978096713/5000000000000000) := by
  have hk1 : kappa q ≤ 0.594385981247 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477886884917 : ℝ)) (s := (0.878421382495 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596302008299 : ℝ) ≤ 0.675150723534 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596302008299 : ℝ)) (Q := (0.596302008299 : ℝ))
      (s := (0.802760185173 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771220615755 : ℝ)) (R := (0.771768299866 : ℝ)) (Q2 := (0.596302008299 : ℝ)) (T := (0.822141226264 : ℝ))
    (B := ((3385784978096713/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S12
namespace BstLean.Part269.S12
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12650 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052589060279 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S12.wn_upper (by omega : 12650 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010618067234 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035880543492)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010618067234 + 2 * 0.737676 / 12650) := by gcongr
    _ ≤ (0.052589060279 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12650 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12650 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.472218792019 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12650 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.472218792019 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12650 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003543786177 + 0.003307136648 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003543786177 + 0.003307136648 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.472218792019 ≤ R)
    (hB : (X + 0.052589060279 + R + 0.008498241865) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008498241865 := by
    convert (BstLean.Part269.S12.finite_centre_upper (by omega : 12650 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (42783224743/500000000000)
  | 2 => (43255303501/500000000000)
  | 3 => (4372655547/50000000000)
  | 4 => (17679085381/200000000000)
  | 5 => (17867865207/200000000000)
  | 6 => (11285866273/125000000000)
  | 7 => (45620380653/500000000000)
  | 8 => (92203795091/1000000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003543786177 + 0.003307136648 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219156920393 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010988202170 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003543786177 + 0.003307136648 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220727319531 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011103396439 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003543786177 + 0.003307136648 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222277224244 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011218210230 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003543786177 + 0.003307136648 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223806843012 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011332651885 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003543786177 + 0.003307136648 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225316379086 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011446729505 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003543786177 + 0.003307136648 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226806029003 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011560450843 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003543786177 + 0.003307136648 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228275984455 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011673823438 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12650 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003543786177 + 0.003307136648 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229726430840 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011786854509 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12650 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g) :
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

end BstLean.Part269.S12

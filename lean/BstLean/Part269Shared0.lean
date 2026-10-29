import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S0
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12350 ≤ n) : wn n ≤ 1.036317588293 := by
  have hnR : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.130553854464 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.130553854464 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036317588293 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12350 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12350 + 24 / (12350 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12350 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008601287531 : ℝ) := by
  have hnR : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.130553854464 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12350 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036317588293 * (81 / 1000 / 12350)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036317588293 * n *
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
        4 * (1 / 2.506628) * 1.036317588293 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036317588293 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036317588293 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12350)) / 111.130553854464 := by gcongr
    _ ≤ (0.008601287531 : ℝ) := by norm_num

end BstLean.Part269.S0
namespace BstLean.Part269.S0
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12350 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12350 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12350 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12350 + 0.008601287531 / 111.130553854464) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12350 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12350 := by gcongr
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
  have hn : (111.130553854464 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S0.finite_centre_upper (by omega : 12350 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (264011183171/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010941075071969/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627910655293 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528022366342 : ℝ)) (s := (0.849230463799 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629918970754 : ℝ) ≤ 0.699116678538 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629918970754 : ℝ)) (Q := (0.629918970754 : ℝ))
      (s := (0.776660859246 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792663556368 : ℝ)) (R := (0.793224544547 : ℝ)) (Q2 := (0.629918970754 : ℝ)) (T := (0.836605834935 : ℝ))
    (B := ((7010941075071969/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16463268843/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1751277296615493/2500000000000000) := by
  have hk1 : kappa q ≤ 0.627098527941 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526824602976 : ℝ)) (s := (0.849974021780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629105346493 : ℝ) ≤ 0.698530915332 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629105346493 : ℝ)) (Q := (0.629105346493 : ℝ))
      (s := (0.777320051854 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792151113261 : ℝ)) (R := (0.792712101440 : ℝ)) (Q2 := (0.629105346493 : ℝ)) (T := (0.836255281427 : ℝ))
    (B := ((1751277296615493/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52562683961/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499641930773687/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626286957555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525626839610 : ℝ)) (s := (0.850715243476 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628292279854 : ℝ) ≤ 0.697945840285 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628292279854 : ℝ)) (Q := (0.628292279854 : ℝ))
      (s := (0.777977384682 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791638690221 : ℝ)) (R := (0.792199678400 : ℝ)) (Q2 := (0.628292279854 : ℝ)) (T := (0.835904992999 : ℝ))
    (B := ((3499641930773687/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131107269061/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6993465089319729/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625475943464 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524429076244 : ℝ)) (s := (0.851454134989 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627479770164 : ℝ) ≤ 0.697361452083 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627479770164 : ℝ)) (Q := (0.627479770164 : ℝ))
      (s := (0.778632864729 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791126286862 : ℝ)) (R := (0.791687275041 : ℝ)) (Q2 := (0.627479770164 : ℝ)) (T := (0.835554969198 : ℝ))
    (B := ((6993465089319729/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523231312879/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1397530571762893/2000000000000000) := by
  have hk1 : kappa q ≤ 0.624665485007 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523231312879 : ℝ)) (s := (0.852190702381 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667816759 : ℝ) ≤ 0.696777749417 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667816759 : ℝ)) (Q := (0.626667816759 : ℝ))
      (s := (0.779286498946 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790613902804 : ℝ)) (R := (0.791174890983 : ℝ)) (Q2 := (0.626667816759 : ℝ)) (T := (0.835205209571 : ℝ))
    (B := ((1397530571762893/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522033549513/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (34909235795553/50000000000000) := by
  have hk1 : kappa q ≤ 0.623855581518 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522033549513 : ℝ)) (s := (0.852924951671 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625856418974 : ℝ) ≤ 0.696194730980 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625856418974 : ℝ)) (Q := (0.625856418974 : ℝ))
      (s := (0.779938294245 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790101537664 : ℝ)) (R := (0.790662525843 : ℝ)) (Q2 := (0.625856418974 : ℝ)) (T := (0.834855713667 : ℝ))
    (B := ((34909235795553/50000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520835786147/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (279041919173219/400000000000000) := by
  have hk1 : kappa q ≤ 0.623046232341 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520835786147 : ℝ)) (s := (0.853656888843 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625045576150 : ℝ) ≤ 0.695612395472 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625045576150 : ℝ)) (Q := (0.625045576150 : ℝ))
      (s := (0.780588257493 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789589191062 : ℝ)) (R := (0.790150179241 : ℝ)) (Q2 := (0.625045576150 : ℝ)) (T := (0.834506481038 : ℝ))
    (B := ((279041919173219/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519638022781/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742563827159869/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622237436818 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519638022781 : ℝ)) (s := (0.854386519838 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624235287628 : ℝ) ≤ 0.695030741593 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624235287628 : ℝ)) (Q := (0.624235287628 : ℝ))
      (s := (0.781236395517 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789076862618 : ℝ)) (R := (0.789637850797 : ℝ)) (Q2 := (0.624235287628 : ℝ)) (T := (0.834157511234 : ℝ))
    (B := ((1742563827159869/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103688051883/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964469136245767/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621429194298 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518440259415 : ℝ)) (s := (0.855113850559 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623425552756 : ℝ) ≤ 0.694449768051 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623425552756 : ℝ)) (Q := (0.623425552756 : ℝ))
      (s := (0.781882715100 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788564551954 : ℝ)) (R := (0.789125540133 : ℝ)) (Q2 := (0.623425552756 : ℝ)) (T := (0.833808803809 : ℝ))
    (B := ((6964469136245767/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517242496049/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (869836181425003/1250000000000000) := by
  have hk1 : kappa q ≤ 0.620621504131 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517242496049 : ℝ)) (s := (0.855838886872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622616370883 : ℝ) ≤ 0.693869473558 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622616370883 : ℝ)) (Q := (0.622616370883 : ℝ))
      (s := (0.782527222983 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788052258693 : ℝ)) (R := (0.788613246872 : ℝ)) (Q2 := (0.622616370883 : ℝ)) (T := (0.833460358320 : ℝ))
    (B := ((869836181425003/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516044732683/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (217278632606099/312500000000000) := by
  have hk1 : kappa q ≤ 0.619814365670 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516044732683 : ℝ)) (s := (0.856561634601 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621807741362 : ℝ) ≤ 0.693289856827 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621807741362 : ℝ)) (Q := (0.621807741362 : ℝ))
      (s := (0.783169925867 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787539982458 : ℝ)) (R := (0.788100970637 : ℝ)) (Q2 := (0.621807741362 : ℝ)) (T := (0.833112174321 : ℝ))
    (B := ((217278632606099/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257423484659/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6947149501566103/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619007778274 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514846969318 : ℝ)) (s := (0.857282099536 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620999663549 : ℝ) ≤ 0.692710916580 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620999663549 : ℝ)) (Q := (0.620999663549 : ℝ))
      (s := (0.783810830413 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787027722875 : ℝ)) (R := (0.787588711054 : ℝ)) (Q2 := (0.620999663549 : ℝ)) (T := (0.832764251372 : ℝ))
    (B := ((6947149501566103/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (8025768843/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3470694607644729/5000000000000000) := by
  have hk1 : kappa q ≤ 0.618201741301 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513649205952 : ℝ)) (s := (0.858000287428 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620192136803 : ℝ) ≤ 0.692132651539 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620192136803 : ℝ)) (Q := (0.620192136803 : ℝ))
      (s := (0.784449943240 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786515479569 : ℝ)) (R := (0.787076467748 : ℝ)) (Q2 := (0.620192136803 : ℝ)) (T := (0.832416589033 : ℝ))
    (B := ((3470694607644729/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256225721293/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (277425414959333/400000000000000) := by
  have hk1 : kappa q ≤ 0.617396254113 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512451442586 : ℝ)) (s := (0.858716203988 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619385160483 : ℝ) ≤ 0.691555060428 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619385160483 : ℝ)) (Q := (0.619385160483 : ℝ))
      (s := (0.785087270929 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786003252165 : ℝ)) (R := (0.786564240344 : ℝ)) (Q2 := (0.619385160483 : ℝ)) (T := (0.832069186862 : ℝ))
    (B := ((277425414959333/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25562683961/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3464943983553503/5000000000000000) := by
  have hk1 : kappa q ≤ 0.616591316079 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511253679220 : ℝ)) (s := (0.859429854895 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618578733956 : ℝ) ≤ 0.690978141982 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618578733956 : ℝ)) (Q := (0.618578733956 : ℝ))
      (s := (0.785722820019 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785491040292 : ℝ)) (R := (0.786052028471 : ℝ)) (Q2 := (0.618578733956 : ℝ)) (T := (0.831722044424 : ℝ))
    (B := ((3464943983553503/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (255027957927/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6924146984160761/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615786926566 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510055915854 : ℝ)) (s := (0.860141245787 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617772856591 : ℝ) ≤ 0.690401894937 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617772856591 : ℝ)) (Q := (0.617772856591 : ℝ))
      (s := (0.786356597009 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784978843579 : ℝ)) (R := (0.785539831758 : ℝ)) (Q2 := (0.617772856591 : ℝ)) (T := (0.831375161283 : ℝ))
    (B := ((6924146984160761/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63607269061/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918412414685553/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614983084948 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508858152488 : ℝ)) (s := (0.860850382266 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616967527758 : ℝ) ≤ 0.689826318032 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616967527758 : ℝ)) (Q := (0.616967527758 : ℝ))
      (s := (0.786988608363 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784466661655 : ℝ)) (R := (0.785027649834 : ℝ)) (Q2 := (0.616967527758 : ℝ)) (T := (0.831028537004 : ℝ))
    (B := ((6918412414685553/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253830194561/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3456342124131401/5000000000000000) := by
  have hk1 : kappa q ≤ 0.614179790600 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507660389122 : ℝ)) (s := (0.861557269900 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616162746834 : ℝ) ≤ 0.689251410012 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616162746834 : ℝ)) (Q := (0.616162746834 : ℝ))
      (s := (0.787618860500 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783954494152 : ℝ)) (R := (0.784515482331 : ℝ)) (Q2 := (0.616162746834 : ℝ)) (T := (0.830682171156 : ℝ))
    (B := ((3456342124131401/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506462625757/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1381392494902827/2000000000000000) := by
  have hk1 : kappa q ≤ 0.613377042901 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506462625757 : ℝ)) (s := (0.862261914219 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615358513193 : ℝ) ≤ 0.688677169624 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615358513193 : ℝ)) (Q := (0.615358513193 : ℝ))
      (s := (0.788247359806 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783442340700 : ℝ)) (R := (0.784003328879 : ℝ)) (Q2 := (0.615358513193 : ℝ)) (T := (0.830336063306 : ℝ))
    (B := ((1381392494902827/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505264862391/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450623541550573/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612574841233 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505264862391 : ℝ)) (s := (0.862964320719 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614554826218 : ℝ) ≤ 0.688103595622 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614554826218 : ℝ)) (Q := (0.614554826218 : ℝ))
      (s := (0.788874112627 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782930200933 : ℝ)) (R := (0.783491189112 : ℝ)) (Q2 := (0.614554826218 : ℝ)) (T := (0.829990213025 : ℝ))
    (B := ((3450623541550573/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20162683961/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895538063725149/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611773184981 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504067099025 : ℝ)) (s := (0.863664494860 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613751685293 : ℝ) ≤ 0.687530686763 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613751685293 : ℝ)) (Q := (0.613751685293 : ℝ))
      (s := (0.789499125269 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782418074485 : ℝ)) (R := (0.782979062664 : ℝ)) (Q2 := (0.613751685293 : ℝ)) (T := (0.829644619886 : ℝ))
    (B := ((6895538063725149/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (502869335659/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889835406126939/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610972073532 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502869335659 : ℝ)) (s := (0.864362442066 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612949089803 : ℝ) ≤ 0.686958441806 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612949089803 : ℝ)) (Q := (0.612949089803 : ℝ))
      (s := (0.790122404005 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781905960990 : ℝ)) (R := (0.782466949169 : ℝ)) (Q2 := (0.612949089803 : ℝ)) (T := (0.829299283461 : ℝ))
    (B := ((6889835406126939/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501671572293/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884139100086553/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610171506280 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501671572293 : ℝ)) (s := (0.865058167729 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612147039143 : ℝ) ≤ 0.686386859521 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612147039143 : ℝ)) (Q := (0.612147039143 : ℝ))
      (s := (0.790743955063 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781393860086 : ℝ)) (R := (0.781954848265 : ℝ)) (Q2 := (0.612147039143 : ℝ)) (T := (0.828954203328 : ℝ))
    (B := ((6884139100086553/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500473808927/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1719612283855759/2500000000000000) := by
  have hk1 : kappa q ≤ 0.609371482619 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500473808927 : ℝ)) (s := (0.865751677203 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611345532703 : ℝ) ≤ 0.685815938674 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611345532703 : ℝ)) (Q := (0.611345532703 : ℝ))
      (s := (0.791363784643 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780881771409 : ℝ)) (R := (0.781442759588 : ℝ)) (Q2 := (0.611345532703 : ℝ)) (T := (0.828609379062 : ℝ))
    (B := ((1719612283855759/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499276045561/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872765501994201/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608572001945 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499276045561 : ℝ)) (s := (0.866442975810 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610544569881 : ℝ) ≤ 0.685245678042 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610544569881 : ℝ)) (Q := (0.610544569881 : ℝ))
      (s := (0.791981898903 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780369694597 : ℝ)) (R := (0.780930682776 : ℝ)) (Q2 := (0.610544569881 : ℝ)) (T := (0.828264810243 : ℝ))
    (B := ((6872765501994201/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (124519570549/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1716772047424101/2500000000000000) := by
  have hk1 : kappa q ≤ 0.607773063661 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498078282196 : ℝ)) (s := (0.867132068837 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609744150076 : ℝ) ≤ 0.684676076401 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609744150076 : ℝ)) (Q := (0.609744150076 : ℝ))
      (s := (0.792598303965 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779857629290 : ℝ)) (R := (0.780418617469 : ℝ)) (Q2 := (0.609744150076 : ℝ)) (T := (0.827920496451 : ℝ))
    (B := ((1716772047424101/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49688051883/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1715354297116077/2500000000000000) := by
  have hk1 : kappa q ≤ 0.606974667170 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496880518830 : ℝ)) (s := (0.867818961540 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608944272691 : ℝ) ≤ 0.684107132535 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608944272691 : ℝ)) (Q := (0.608944272691 : ℝ))
      (s := (0.793213005918 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779345575127 : ℝ)) (R := (0.779906563306 : ℝ)) (Q2 := (0.608944272691 : ℝ)) (T := (0.827576437268 : ℝ))
    (B := ((1715354297116077/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61960344433/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3427876244135327/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606176811879 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495682755464 : ℝ)) (s := (0.868503659138 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608144937133 : ℝ) ≤ 0.683538845231 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608144937133 : ℝ)) (Q := (0.608144937133 : ℝ))
      (s := (0.793826010811 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778833531751 : ℝ)) (R := (0.779394519930 : ℝ)) (Q2 := (0.608144937133 : ℝ)) (T := (0.827232632277 : ℝ))
    (B := ((3427876244135327/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247242496049/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6850094079126039/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605379497200 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494484992098 : ℝ)) (s := (0.869186166820 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607346142811 : ℝ) ≤ 0.682971213280 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607346142811 : ℝ)) (Q := (0.607346142811 : ℝ))
      (s := (0.794437324660 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778321498804 : ℝ)) (R := (0.778882486983 : ℝ)) (Q2 := (0.607346142811 : ℝ)) (T := (0.826889081064 : ℝ))
    (B := ((6850094079126039/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123321807183/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844441951078689/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604582722545 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493287228732 : ℝ)) (s := (0.869866489739 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606547889137 : ℝ) ≤ 0.682404235478 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606547889137 : ℝ)) (Q := (0.606547889137 : ℝ))
      (s := (0.795046953446 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777809475929 : ℝ)) (R := (0.778370464108 : ℝ)) (Q2 := (0.606547889137 : ℝ)) (T := (0.826545783216 : ℝ))
    (B := ((6844441951078689/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246044732683/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1367759218842847/2000000000000000) := by
  have hk1 : kappa q ≤ 0.603786487332 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492089465366 : ℝ)) (s := (0.870544633018 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605750175528 : ℝ) ≤ 0.681837910625 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605750175528 : ℝ)) (Q := (0.605750175528 : ℝ))
      (s := (0.795654903114 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777297462772 : ℝ)) (R := (0.777858450951 : ℝ)) (Q2 := (0.605750175528 : ℝ)) (T := (0.826202738323 : ℝ))
    (B := ((1367759218842847/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245445851/500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1708289124663873/2500000000000000) := by
  have hk1 : kappa q ≤ 0.602990790980 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490891702000 : ℝ)) (s := (0.871220601747 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604953001402 : ℝ) ≤ 0.681272237526 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604953001402 : ℝ)) (Q := (0.604953001402 : ℝ))
      (s := (0.796261179573 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776785458978 : ℝ)) (R := (0.777346447157 : ℝ)) (Q2 := (0.604953001402 : ℝ)) (T := (0.825859945974 : ℝ))
    (B := ((1708289124663873/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97938787727/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827523154562243/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602195632913 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489693938635 : ℝ)) (s := (0.871894400983 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604156366182 : ℝ) ≤ 0.680707214989 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604156366182 : ℝ)) (Q := (0.604156366182 : ℝ))
      (s := (0.796865788701 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776273464195 : ℝ)) (R := (0.776834452374 : ℝ)) (Q2 := (0.604156366182 : ℝ)) (T := (0.825517405762 : ℝ))
    (B := ((6827523154562243/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488496175269/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821896052131019/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601401012555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488496175269 : ℝ)) (s := (0.872566035752 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603360269291 : ℝ) ≤ 0.680142841827 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603360269291 : ℝ)) (Q := (0.603360269291 : ℝ))
      (s := (0.797468736341 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775761478069 : ℝ)) (R := (0.776322466248 : ℝ)) (Q2 := (0.603360269291 : ℝ)) (T := (0.825175117281 : ℝ))
    (B := ((6821896052131019/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487298411903/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1704068795398721/2500000000000000) := by
  have hk1 : kappa q ≤ 0.600606929338 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487298411903 : ℝ)) (s := (0.873235511049 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602564710158 : ℝ) ≤ 0.679579116857 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602564710158 : ℝ)) (Q := (0.602564710158 : ℝ))
      (s := (0.798070028301 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775249500250 : ℝ)) (R := (0.775810488429 : ℝ)) (Q2 := (0.602564710158 : ℝ)) (T := (0.824833080125 : ℝ))
    (B := ((1704068795398721/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486100648537/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810660533223221/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599813382693 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486100648537 : ℝ)) (s := (0.873902831837 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601769688216 : ℝ) ≤ 0.679016038902 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601769688216 : ℝ)) (Q := (0.601769688216 : ℝ))
      (s := (0.798669670355 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774737530389 : ℝ)) (R := (0.775298518568 : ℝ)) (Q2 := (0.601769688216 : ℝ)) (T := (0.824491293894 : ℝ))
    (B := ((6810660533223221/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484902885171/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1701263024330381/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599020372055 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484902885171 : ℝ)) (s := (0.874568003047 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600975202898 : ℝ) ≤ 0.678453606787 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600975202898 : ℝ)) (Q := (0.600975202898 : ℝ))
      (s := (0.799267668245 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774225568136 : ℝ)) (R := (0.774786556315 : ℝ)) (Q2 := (0.600975202898 : ℝ)) (T := (0.824149758186 : ℝ))
    (B := ((1701263024330381/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96741024361/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799449864231181/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598227896865 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483705121805 : ℝ)) (s := (0.875231029580 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600181253644 : ℝ) ≤ 0.677891819344 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600181253644 : ℝ)) (Q := (0.600181253644 : ℝ))
      (s := (0.799864027679 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773713613145 : ℝ)) (R := (0.774274601324 : ℝ)) (Q2 := (0.600181253644 : ℝ)) (T := (0.823808472603 : ℝ))
    (B := ((6799449864231181/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482507358439/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (679385382432927/1000000000000000) := by
  have hk1 : kappa q ≤ 0.597435956563 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482507358439 : ℝ)) (s := (0.875891916308 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599387839891 : ℝ) ≤ 0.677330675405 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599387839891 : ℝ)) (Q := (0.599387839891 : ℝ))
      (s := (0.800458754335 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773201665068 : ℝ)) (R := (0.773762653247 : ℝ)) (Q2 := (0.599387839891 : ℝ)) (T := (0.823467436745 : ℝ))
    (B := ((679385382432927/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240654797537/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1357652793605671/2000000000000000) := by
  have hk1 : kappa q ≤ 0.596644550595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481309595074 : ℝ)) (s := (0.876550668068 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598594961086 : ℝ) ≤ 0.676770173811 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598594961086 : ℝ)) (Q := (0.598594961086 : ℝ))
      (s := (0.801051853854 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772689723560 : ℝ)) (R := (0.773250711739 : ℝ)) (Q2 := (0.598594961086 : ℝ)) (T := (0.823126650218 : ℝ))
    (B := ((1357652793605671/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120027957927/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3391339836889417/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595853678408 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480111831708 : ℝ)) (s := (0.877207289673 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597802616674 : ℝ) ≤ 0.676210313404 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597802616674 : ℝ)) (Q := (0.597802616674 : ℝ))
      (s := (0.801643331849 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772177788277 : ℝ)) (R := (0.772738776456 : ℝ)) (Q2 := (0.597802616674 : ℝ)) (T := (0.822786112628 : ℝ))
    (B := ((3391339836889417/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (239457034171/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (847137615834921/1250000000000000) := by
  have hk1 : kappa q ≤ 0.595063339453 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478914068342 : ℝ)) (s := (0.877861785901 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597010806106 : ℝ) ≤ 0.675651093032 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597010806106 : ℝ)) (Q := (0.597010806106 : ℝ))
      (s := (0.802233193899 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771665858875 : ℝ)) (R := (0.772226847054 : ℝ)) (Q2 := (0.597010806106 : ℝ)) (T := (0.822445823583 : ℝ))
    (B := ((847137615834921/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12350 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (29857269061/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771528337334509/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594273533185 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477716304976 : ℝ)) (s := (0.878514161503 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596219528837 : ℝ) ≤ 0.675092511548 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596219528837 : ℝ)) (Q := (0.596219528837 : ℝ))
      (s := (0.802821445549 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771153935013 : ℝ)) (R := (0.771714923192 : ℝ)) (Q2 := (0.596219528837 : ℝ)) (T := (0.822105782693 : ℝ))
    (B := ((6771528337334509/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S0
namespace BstLean.Part269.S0
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12350 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.053230942514 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S0.wn_upper (by omega : 12350 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010746257799 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036317588293)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010746257799 + 2 * 0.737676 / 12350) := by gcongr
    _ ≤ (0.053230942514 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12350 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12350 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.130553854464 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12350 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.130553854464 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12350 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.004104440387 + 0.003390347157 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004104440387 + 0.003390347157 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.130553854464 ≤ R)
    (hB : (X + 0.053230942514 + R + 0.008601287531) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008601287531 := by
    convert (BstLean.Part269.S0.finite_centre_upper (by omega : 12350 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (86505635841/1000000000000)
  | 2 => (5466786839/62500000000)
  | 3 => (17686574461/200000000000)
  | 4 => (44700308967/500000000000)
  | 5 => (11296797479/125000000000)
  | 6 => (91357190371/1000000000000)
  | 7 => (18470524887/200000000000)
  | 8 => (23341216973/250000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.004104440387 + 0.003390347157 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011120861327 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.004104440387 + 0.003390347157 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011237446321 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.004104440387 + 0.003390347157 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011353646245 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.004104440387 + 0.003390347157 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011469469539 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.004104440387 + 0.003390347157 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011584924404 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.004104440387 + 0.003390347157 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011700018684 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.004104440387 + 0.003390347157 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011814760012 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12350 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.004104440387 + 0.003390347157 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011929155693 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12350 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g) :
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

end BstLean.Part269.S0

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S5
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12475 ≤ n) : wn n ≤ 1.036133559766 := by
  have hnR : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.691539518443 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.691539518443 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036133559766 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12475 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12475 + 24 / (12475 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12475 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008557898938 : ℝ) := by
  have hnR : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.691539518443 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12475 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036133559766 * (81 / 1000 / 12475)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036133559766 * n *
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
        4 * (1 / 2.506628) * 1.036133559766 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036133559766 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036133559766 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12475)) / 111.691539518443 := by gcongr
    _ ≤ (0.008557898938 : ℝ) := by norm_num

end BstLean.Part269.S5
namespace BstLean.Part269.S5
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12475 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12475 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12475 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12475 + 0.008557898938 / 111.691539518443) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12475 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12475 := by gcongr
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
  have hn : (111.691539518443 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S5.finite_centre_upper (by omega : 12475 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528036181049/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7010679558368551/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627920025421 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528036181049 : ℝ)) (s := (0.849221874132 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629915366228 : ℝ) ≤ 0.699114082851 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629915366228 : ℝ)) (Q := (0.629915366228 : ℝ))
      (s := (0.776663782721 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792666907992 : ℝ)) (R := (0.793222275047 : ℝ)) (Q2 := (0.629915366228 : ℝ)) (T := (0.836604281854 : ℝ))
    (B := ((7010679558368551/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263419899577/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1400970919830709/2000000000000000) := by
  have hk1 : kappa q ≤ 0.627108828016 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526839799154 : ℝ)) (s := (0.849964602809 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629102679394 : ℝ) ≤ 0.698528995644 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629102679394 : ℝ)) (Q := (0.629102679394 : ℝ))
      (s := (0.777322210399 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792155054027 : ℝ)) (R := (0.792710421082 : ℝ)) (Q2 := (0.629102679394 : ℝ)) (T := (0.836254132336 : ℝ))
    (B := ((1400970919830709/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525643417259/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6999036188294259/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626298186300 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525643417259 : ℝ)) (s := (0.850705000510 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628290548899 : ℝ) ≤ 0.697944595012 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628290548899 : ℝ)) (Q := (0.628290548899 : ℝ))
      (s := (0.777978782593 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791643220083 : ℝ)) (R := (0.792198587138 : ℝ)) (Q2 := (0.628290548899 : ℝ)) (T := (0.835904247289 : ℝ))
    (B := ((6999036188294259/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524447035363/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1398644862964117/2000000000000000) := by
  have hk1 : kappa q ≤ 0.625488099607 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524447035363 : ℝ)) (s := (0.851443073317 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478974082 : ℝ) ≤ 0.697360879651 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478974082 : ℝ)) (Q := (0.627478974082 : ℝ))
      (s := (0.778633506270 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791131405780 : ℝ)) (R := (0.791686772835 : ℝ)) (Q2 := (0.627478974082 : ℝ)) (T := (0.835554626263 : ℝ))
    (B := ((1398644862964117/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130812663367/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1397483793561217/2000000000000000) := by
  have hk1 : kappa q ≤ 0.624678567275 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523250653468 : ℝ)) (s := (0.852178827269 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667954274 : ℝ) ≤ 0.696777848250 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667954274 : ℝ)) (Q := (0.626667954274 : ℝ))
      (s := (0.779286388362 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790619610735 : ℝ)) (R := (0.791174977790 : ℝ)) (Q2 := (0.626667954274 : ℝ)) (T := (0.835205268805 : ℝ))
    (B := ((1397483793561217/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (522054271573/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981620136367711/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623869588644 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522054271573 : ℝ)) (s := (0.852912268368 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625857488816 : ℝ) ≤ 0.696195499513 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625857488816 : ℝ)) (Q := (0.625857488816 : ℝ))
      (s := (0.779937435756 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790107834569 : ℝ)) (R := (0.790663201624 : ℝ)) (Q2 := (0.625857488816 : ℝ)) (T := (0.834856174468 : ℝ))
    (B := ((6981620136367711/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (260428944839/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3487913904832769/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623061163058 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520857889678 : ℝ)) (s := (0.853643402576 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625047577053 : ℝ) ≤ 0.695613832142 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625047577053 : ℝ)) (Q := (0.625047577053 : ℝ))
      (s := (0.780586655293 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789596076904 : ℝ)) (R := (0.790151443959 : ℝ)) (Q2 := (0.625047577053 : ℝ)) (T := (0.834507342804 : ℝ))
    (B := ((3487913904832769/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519661507783/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6970041976902487/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622253289862 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519661507783 : ℝ)) (s := (0.854372235814 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624238218325 : ℝ) ≤ 0.695032844841 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624238218325 : ℝ)) (Q := (0.624238218325 : ℝ))
      (s := (0.781234053779 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789084337359 : ℝ)) (R := (0.789639704414 : ℝ)) (Q2 := (0.624238218325 : ℝ)) (T := (0.834158773364 : ℝ))
    (B := ((6970041976902487/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1012627199/1953125000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964262627324063/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621445968407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518465125888 : ℝ)) (s := (0.855098773966 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623429411985 : ℝ) ≤ 0.694452536324 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623429411985 : ℝ)) (Q := (0.623429411985 : ℝ))
      (s := (0.781879637970 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788572615560 : ℝ)) (R := (0.789127982615 : ℝ)) (Q2 := (0.623429411985 : ℝ)) (T := (0.833810465706 : ℝ))
    (B := ((6964262627324063/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64658592999/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1391697950043617/2000000000000000) := by
  have hk1 : kappa q ≤ 0.620639198044 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517268743992 : ℝ)) (s := (0.855823022879 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622621157380 : ℝ) ≤ 0.693872905304 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622621157380 : ℝ)) (Q := (0.622621157380 : ℝ))
      (s := (0.782523414591 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788060911128 : ℝ)) (R := (0.788616278183 : ℝ)) (Q2 := (0.622621157380 : ℝ)) (T := (0.833462419385 : ℝ))
    (B := ((1391697950043617/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516072362097/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (278108933396577/400000000000000) := by
  have hk1 : kappa q ≤ 0.619832978131 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516072362097 : ℝ)) (s := (0.856544988358 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621813453869 : ℝ) ≤ 0.693293950503 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621813453869 : ℝ)) (Q := (0.621813453869 : ℝ))
      (s := (0.783165390316 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787549223690 : ℝ)) (R := (0.788104590745 : ℝ)) (Q2 := (0.621813453869 : ℝ)) (T := (0.833114633960 : ℝ))
    (B := ((278108933396577/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257437990101/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389392674156949/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619027308025 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514875980202 : ℝ)) (s := (0.857264676172 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621006300808 : ℝ) ≤ 0.692715670642 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621006300808 : ℝ)) (Q := (0.621006300808 : ℝ))
      (s := (0.783805571783 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787037552871 : ℝ)) (R := (0.787592919926 : ℝ)) (Q2 := (0.621006300808 : ℝ)) (T := (0.832767108990 : ℝ))
    (B := ((1389392674156949/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513679598307/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6941209847242241/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618222187089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513679598307 : ℝ)) (s := (0.857982092053 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620199697557 : ℝ) ≤ 0.692138064450 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620199697557 : ℝ)) (Q := (0.620199697557 : ℝ))
      (s := (0.784443965590 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786525898298 : ℝ)) (R := (0.787081265353 : ℝ)) (Q2 := (0.620199697557 : ℝ)) (T := (0.832419844036 : ℝ))
    (B := ((6941209847242241/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128120804103/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1387092550748277/2000000000000000) := by
  have hk1 : kappa q ≤ 0.617417614688 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512483216412 : ℝ)) (s := (0.858697241696 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619393643481 : ℝ) ≤ 0.691561130657 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619393643481 : ℝ)) (Q := (0.619393643481 : ℝ))
      (s := (0.785080578295 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786014259598 : ℝ)) (R := (0.786569626653 : ℝ)) (Q2 := (0.619393643481 : ℝ)) (T := (0.832072838661 : ℝ))
    (B := ((1387092550748277/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511286834517/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (692972207977767/1000000000000000) := by
  have hk1 : kappa q ≤ 0.616613590191 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511286834517 : ℝ)) (s := (0.859410130759 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618588137948 : ℝ) ≤ 0.690984868002 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618588137948 : ℝ)) (Q := (0.618588137948 : ℝ))
      (s := (0.785715416414 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785502636402 : ℝ)) (R := (0.786058003457 : ℝ)) (Q2 := (0.618588137948 : ℝ)) (T := (0.831726092429 : ℝ))
    (B := ((692972207977767/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510090452621/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (21637461921523/31250000000000) := by
  have hk1 : kappa q ≤ 0.615810112967 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510090452621 : ℝ)) (s := (0.860120764861 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617783180326 : ℝ) ≤ 0.690409275221 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617783180326 : ℝ)) (Q := (0.617783180326 : ℝ))
      (s := (0.786348486428 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784991028338 : ℝ)) (R := (0.785546395393 : ℝ)) (Q2 := (0.617783180326 : ℝ)) (T := (0.831379604904 : ℝ))
    (B := ((21637461921523/31250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (254447035363/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3459129974323619/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615007182393 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508894070726 : ℝ)) (s := (0.860829149588 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616978769991 : ℝ) ≤ 0.689834351062 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616978769991 : ℝ)) (Q := (0.616978769991 : ℝ))
      (s := (0.786979794773 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784479435038 : ℝ)) (R := (0.785034802093 : ℝ)) (Q2 := (0.616978769991 : ℝ)) (T := (0.831033375656 : ℝ))
    (B := ((3459129974323619/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507697688831/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912538470674359/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614204797847 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507697688831 : ℝ)) (s := (0.861535290488 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616174906318 : ℝ) ≤ 0.689260094271 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616174906318 : ℝ)) (Q := (0.616174906318 : ℝ))
      (s := (0.787609347853 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783967856134 : ℝ)) (R := (0.784523223189 : ℝ)) (Q2 := (0.616174906318 : ℝ)) (T := (0.830687404251 : ℝ))
    (B := ((6912538470674359/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63312663367/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906823370625807/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613402958708 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506501306936 : ℝ)) (s := (0.862239193074 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615371588687 : ℝ) ≤ 0.688686503602 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615371588687 : ℝ)) (Q := (0.615371588687 : ℝ))
      (s := (0.788237152028 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783456291258 : ℝ)) (R := (0.784011658313 : ℝ)) (Q2 := (0.615371588687 : ℝ)) (T := (0.830341690262 : ℝ))
    (B := ((6906823370625807/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505304925041/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (431319664887403/625000000000000) := by
  have hk1 : kappa q ≤ 0.612601664361 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505304925041 : ℝ)) (s := (0.862940862823 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614568816482 : ℝ) ≤ 0.688113577812 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614568816482 : ℝ)) (Q := (0.614568816482 : ℝ))
      (s := (0.788863213624 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782944740046 : ℝ)) (R := (0.783500107101 : ℝ)) (Q2 := (0.614568816482 : ℝ)) (T := (0.829996233260 : ℝ))
    (B := ((431319664887403/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252054271573/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895412263128691/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611800914194 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504108543146 : ℝ)) (s := (0.863640305178 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613766589088 : ℝ) ≤ 0.687541315661 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613766589088 : ℝ)) (Q := (0.613766589088 : ℝ))
      (s := (0.789487538926 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782433202132 : ℝ)) (R := (0.782988569187 : ℝ)) (Q2 := (0.613766589088 : ℝ)) (T := (0.829651032817 : ℝ))
    (B := ((6895412263128691/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (402329729/800000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889716235192247/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611000707595 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502912161250 : ℝ)) (s := (0.864337525546 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612964905893 : ℝ) ≤ 0.686969715915 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612964905893 : ℝ)) (Q := (0.612964905893 : ℝ))
      (s := (0.790110134187 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781921677151 : ℝ)) (R := (0.782477044206 : ℝ)) (Q2 := (0.612964905893 : ℝ)) (T := (0.829306088510 : ℝ))
    (B := ((6889716235192247/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100343155871/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884026544203893/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610201043959 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501715779355 : ℝ)) (s := (0.865032529300 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612163766292 : ℝ) ≤ 0.686398777345 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612163766292 : ℝ)) (Q := (0.612163766292 : ℝ))
      (s := (0.790731005614 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781410164743 : ℝ)) (R := (0.781965531798 : ℝ)) (Q2 := (0.612163766292 : ℝ)) (T := (0.828961399917 : ℝ))
    (B := ((6884026544203893/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25025969873/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878343180017237/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609401922683 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500519397460 : ℝ)) (s := (0.865725321778 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611363169679 : ℝ) ≤ 0.685828498723 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611363169679 : ℝ)) (Q := (0.611363169679 : ℝ))
      (s := (0.791350159386 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780898664544 : ℝ)) (R := (0.781454031599 : ℝ)) (Q2 := (0.611363169679 : ℝ)) (T := (0.828616966613 : ℝ))
    (B := ((6878343180017237/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99864603113/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3436333066262243/5000000000000000) := by
  have hk1 : kappa q ≤ 0.608603343167 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499323015565 : ℝ)) (s := (0.866415908284 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610563115454 : ℝ) ≤ 0.685258878829 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610563115454 : ℝ)) (Q := (0.610563115454 : ℝ))
      (s := (0.791967601640 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780387176196 : ℝ)) (R := (0.780942543251 : ℝ)) (Q2 := (0.610563115454 : ℝ)) (T := (0.828272788181 : ℝ))
    (B := ((3436333066262243/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49812663367/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6866995391656211/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607805304812 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498126633670 : ℝ)) (s := (0.867104294090 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609763603017 : ℝ) ≤ 0.684689916444 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609763603017 : ℝ)) (Q := (0.609763603017 : ℝ))
      (s := (0.792583338480 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779875699337 : ℝ)) (R := (0.780431066392 : ℝ)) (Q2 := (0.609763603017 : ℝ)) (T := (0.827928864202 : ℝ))
    (B := ((6866995391656211/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19877210071/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430665473690561/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607007807026 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496930251775 : ℝ)) (s := (0.867790484433 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608964631774 : ℝ) ≤ 0.684121610356 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608964631774 : ℝ)) (Q := (0.608964631774 : ℝ))
      (s := (0.793197375972 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779364233610 : ℝ)) (R := (0.779919600665 : ℝ)) (Q2 := (0.608964631774 : ℝ)) (T := (0.827585194259 : ℝ))
    (B := ((3430665473690561/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495733869879/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855672789705837/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606210849216 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495733869879 : ℝ)) (s := (0.868474484516 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608166201132 : ℝ) ≤ 0.683553959355 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608166201132 : ℝ)) (Q := (0.608166201132 : ℝ))
      (s := (0.793809720148 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778852778656 : ℝ)) (R := (0.779408145711 : ℝ)) (Q2 := (0.608166201132 : ℝ)) (T := (0.827241777937 : ℝ))
    (B := ((6855672789705837/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30908592999/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (342501045433733/500000000000000) := by
  have hk1 : kappa q ≤ 0.605414430797 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494537487984 : ℝ)) (s := (0.869156299511 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607368310504 : ℝ) ≤ 0.682986962237 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607368310504 : ℝ)) (Q := (0.607368310504 : ℝ))
      (s := (0.794420377002 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778341334121 : ℝ)) (R := (0.778896701176 : ℝ)) (Q2 := (0.607368310504 : ℝ)) (T := (0.826898614823 : ℝ))
    (B := ((342501045433733/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493341106089/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1368875058873871/2000000000000000) := by
  have hk1 : kappa q ≤ 0.604618551182 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493341106089 : ℝ)) (s := (0.869835934555 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606570959303 : ℝ) ≤ 0.682420617802 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606570959303 : ℝ)) (Q := (0.606570959303 : ℝ))
      (s := (0.795029352497 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777829899648 : ℝ)) (R := (0.778385266703 : ℝ)) (Q2 := (0.606570959303 : ℝ)) (T := (0.826555704506 : ℝ))
    (B := ((1368875058873871/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246072362097/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (53427624507101/78125000000000) := by
  have hk1 : kappa q ≤ 0.603823209792 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492144724194 : ℝ)) (s := (0.870513394756 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605774146948 : ℝ) ≤ 0.681854924855 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605774146948 : ℝ)) (Q := (0.605774146948 : ℝ))
      (s := (0.795636652556 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777318474884 : ℝ)) (R := (0.777873841939 : ℝ)) (Q2 := (0.605774146948 : ℝ)) (T := (0.826213046576 : ℝ))
    (B := ((53427624507101/78125000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (490948342299/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416551413224701/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603028406048 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490948342299 : ℝ)) (s := (0.871188685185 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604977872859 : ℝ) ≤ 0.681289882202 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604977872859 : ℝ)) (Q := (0.604977872859 : ℝ))
      (s := (0.796242283072 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776807059476 : ℝ)) (R := (0.777362426531 : ℝ)) (Q2 := (0.604977872859 : ℝ)) (T := (0.825870640624 : ℝ))
    (B := ((3416551413224701/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122437990101/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1706868988295901/2500000000000000) := by
  have hk1 : kappa q ≤ 0.602234139374 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489751960404 : ℝ)) (s := (0.871861810886 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604182136461 : ℝ) ≤ 0.680725488658 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604182136461 : ℝ)) (Q := (0.604182136461 : ℝ))
      (s := (0.796846249902 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776295653072 : ℝ)) (R := (0.776851020127 : ℝ)) (Q2 := (0.604182136461 : ℝ)) (T := (0.825528486246 : ℝ))
    (B := ((1706868988295901/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122138894627/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3410927653670473/5000000000000000) := by
  have hk1 : kappa q ≤ 0.601440409197 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488555578508 : ℝ)) (s := (0.872532776868 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603386937176 : ℝ) ≤ 0.680161743036 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603386937176 : ℝ)) (Q := (0.603386937176 : ℝ))
      (s := (0.797448558871 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775784255319 : ℝ)) (R := (0.776339622374 : ℝ)) (Q2 := (0.603386937176 : ℝ)) (T := (0.825186583033 : ℝ))
    (B := ((3410927653670473/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487359196613/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816240879187211/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600647214952 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487359196613 : ℝ)) (s := (0.873201588110 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602592274441 : ℝ) ≤ 0.679598644163 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602592274441 : ℝ)) (Q := (0.602592274441 : ℝ))
      (s := (0.798049215766 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775272865871 : ℝ)) (R := (0.775828232926 : ℝ)) (Q2 := (0.602592274441 : ℝ)) (T := (0.824844930587 : ℝ))
    (B := ((6816240879187211/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243081407359/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405316329512171/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599854556069 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486162814718 : ℝ)) (s := (0.873868249558 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601798147684 : ℝ) ≤ 0.679036190859 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601798147684 : ℝ)) (Q := (0.601798147684 : ℝ))
      (s := (0.798648226346 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774761484376 : ℝ)) (R := (0.775316851431 : ℝ)) (Q2 := (0.601798147684 : ℝ)) (T := (0.824503528502 : ℝ))
    (B := ((3405316329512171/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484966432823/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (850628829648779/1250000000000000) := by
  have hk1 : kappa q ≤ 0.599062431989 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484966432823 : ℝ)) (s := (0.874532766130 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601004556346 : ℝ) ≤ 0.678474381959 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601004556346 : ℝ)) (Q := (0.601004556346 : ℝ))
      (s := (0.799245596330 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774250110489 : ℝ)) (R := (0.774805477544 : ℝ)) (Q2 := (0.601004556346 : ℝ)) (T := (0.824162376383 : ℝ))
    (B := ((850628829648779/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30235628183/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (424964675253657/625000000000000) := by
  have hk1 : kappa q ≤ 0.598270842150 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483770050928 : ℝ)) (s := (0.875195142712 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600211499864 : ℝ) ≤ 0.677913216294 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600211499864 : ℝ)) (Q := (0.600211499864 : ℝ))
      (s := (0.799841331410 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773738743863 : ℝ)) (R := (0.774294110918 : ℝ)) (Q2 := (0.600211499864 : ℝ)) (T := (0.823821473829 : ℝ))
    (B := ((424964675253657/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482573669033/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (849230643754793/1250000000000000) := by
  have hk1 : kappa q ≤ 0.597479785997 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482573669033 : ℝ)) (s := (0.875855384157 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599418977679 : ℝ) ≤ 0.677352692703 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599418977679 : ℝ)) (Q := (0.599418977679 : ℝ))
      (s := (0.800435437246 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773227384151 : ℝ)) (R := (0.773782751206 : ℝ)) (Q2 := (0.599418977679 : ℝ)) (T := (0.823480820444 : ℝ))
    (B := ((849230643754793/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481377287137/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (339413083278711/500000000000000) := by
  have hk1 : kappa q ≤ 0.596689262975 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481377287137 : ℝ)) (s := (0.876513495292 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598626989237 : ℝ) ≤ 0.676792810028 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598626989237 : ℝ)) (Q := (0.598626989237 : ℝ))
      (s := (0.801027919462 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772716031009 : ℝ)) (R := (0.773271398064 : ℝ)) (Q2 := (0.598626989237 : ℝ)) (T := (0.823140415835 : ℝ))
    (B := ((339413083278711/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240090452621/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782683451285471/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595899272536 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480180905242 : ℝ)) (s := (0.877169480911 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597835533991 : ℝ) ≤ 0.676233567119 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597835533991 : ℝ)) (Q := (0.597835533991 : ℝ))
      (s := (0.801618783649 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772204684096 : ℝ)) (R := (0.772760051151 : ℝ)) (Q2 := (0.597835533991 : ℝ)) (T := (0.822800259610 : ℝ))
    (B := ((6782683451285471/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478984523347/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3388555533512421/5000000000000000) := by
  have hk1 : kappa q ≤ 0.595109814131 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478984523347 : ℝ)) (s := (0.877823345779 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597044611389 : ℝ) ≤ 0.675674962824 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597044611389 : ℝ)) (Q := (0.597044611389 : ℝ))
      (s := (0.802208035370 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771693343068 : ℝ)) (R := (0.772248710123 : ℝ)) (Q2 := (0.597044611389 : ℝ)) (T := (0.822460351375 : ℝ))
    (B := ((3388555533512421/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12475 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (119447035363/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (846443103315521/1250000000000000) := by
  have hk1 : kappa q ≤ 0.594320887218 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477788141452 : ℝ)) (s := (0.878475094632 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596254220886 : ℝ) ≤ 0.675116996001 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596254220886 : ℝ)) (Q := (0.596254220886 : ℝ))
      (s := (0.802795680156 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771182007584 : ℝ)) (R := (0.771737374639 : ℝ)) (Q2 := (0.596254220886 : ℝ)) (T := (0.822120690744 : ℝ))
    (B := ((846443103315521/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S5
namespace BstLean.Part269.S5
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12475 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052960658316 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S5.wn_upper (by omega : 12475 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010692283285 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036133559766)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010692283285 + 2 * 0.737676 / 12475) := by gcongr
    _ ≤ (0.052960658316 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12475 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12475 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.691539518443 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12475 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.691539518443 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12475 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003790088722 + 0.003355178034 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003790088722 + 0.003355178034 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.691539518443 ≤ R)
    (hB : (X + 0.052960658316 + R + 0.008557898938) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008557898938 := by
    convert (BstLean.Part269.S5.finite_centre_upper (by omega : 12475 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (86099915337/1000000000000)
  | 2 => (87054416349/1000000000000)
  | 3 => (17601771721/200000000000)
  | 4 => (22241267131/250000000000)
  | 5 => (89925240613/1000000000000)
  | 6 => (45445995101/500000000000)
  | 7 => (45934205393/500000000000)
  | 8 => (2321453399/25000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003790088722 + 0.003355178034 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219769990697 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011065005317 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003790088722 + 0.003355178034 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.221336821108 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011181004747 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003790088722 + 0.003355178034 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222883263042 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011296621041 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003790088722 + 0.003355178034 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224409521281 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011411862597 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003790088722 + 0.003355178034 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225915795560 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011526737575 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003790088722 + 0.003355178034 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227402279071 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011641253779 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003790088722 + 0.003355178034 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228869160329 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011755418803 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12475 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003790088722 + 0.003355178034 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.230316621705 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011869239916 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12475 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g) :
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

end BstLean.Part269.S5

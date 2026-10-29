import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S23
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12925 ≤ n) : wn n ≤ 1.035493437527 := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.688170009020 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.688170009020 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035493437527 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12925 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12925 + 24 / (12925 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12925 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008406961539 : ℝ) := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.688170009020 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12925 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035493437527 * (81 / 1000 / 12925)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035493437527 * n *
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
        4 * (1 / 2.506628) * 1.035493437527 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035493437527 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035493437527 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12925)) / 113.688170009020 := by gcongr
    _ ≤ (0.008406961539 : ℝ) := by norm_num

end BstLean.Part269.S23
namespace BstLean.Part269.S23
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12925 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12925 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12925 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12925 + 0.008406961539 / 113.688170009020) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12925 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12925 := by gcongr
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
  have hn : (113.688170009020 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S23.finite_centre_upper (by omega : 12925 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528084213071/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1752445614494661/2500000000000000) := by
  have hk1 : kappa q ≤ 0.627952604770 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528084213071 : ℝ)) (s := (0.849192006501 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629903315313 : ℝ) ≤ 0.699105404801 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629903315313 : ℝ)) (Q := (0.629903315313 : ℝ))
      (s := (0.776673556495 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792678656182 : ℝ)) (R := (0.793214687440 : ℝ)) (Q2 := (0.629903315313 : ℝ)) (T := (0.836599089485 : ℝ))
    (B := ((1752445614494661/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263446317189/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7003981577362477/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627144640794 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526892634378 : ℝ)) (s := (0.849931851291 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629093887591 : ℝ) ≤ 0.698522667624 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629093887591 : ℝ)) (Q := (0.629093887591 : ℝ))
      (s := (0.777329325702 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792168850682 : ℝ)) (R := (0.792704881940 : ℝ)) (Q2 := (0.629093887591 : ℝ)) (T := (0.836250344487 : ℝ))
    (B := ((7003981577362477/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105140211137/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27336668718453/39062500000000) := by
  have hk1 : kappa q ≤ 0.626337228082 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525701055685 : ℝ)) (s := (0.850669383517 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628285011778 : ℝ) ≤ 0.697940611538 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628285011778 : ℝ)) (Q := (0.628285011778 : ℝ))
      (s := (0.777983254303 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791659065051 : ℝ)) (R := (0.792195096309 : ℝ)) (Q2 := (0.628285011778 : ℝ)) (T := (0.835901861851 : ℝ))
    (B := ((27336668718453/39062500000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4097730289/7812500000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (874049911353197/1250000000000000) := by
  have hk1 : kappa q ≤ 0.625530365979 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524509476992 : ℝ)) (s := (0.851404609188 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627476687221 : ℝ) ≤ 0.697359235256 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627476687221 : ℝ)) (Q := (0.627476687221 : ℝ))
      (s := (0.778635349181 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791149298916 : ℝ)) (R := (0.791685330174 : ℝ)) (Q2 := (0.627476687221 : ℝ)) (T := (0.835553641133 : ℝ))
    (B := ((874049911353197/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523317898299/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986617863272729/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624724053827 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523317898299 : ℝ)) (s := (0.852137534275 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668913260 : ℝ) ≤ 0.696778537485 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668913260 : ℝ)) (Q := (0.626668913260 : ℝ))
      (s := (0.779285617187 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790639551897 : ℝ)) (R := (0.791175583155 : ℝ)) (Q2 := (0.626668913260 : ℝ)) (T := (0.835205681887 : ℝ))
    (B := ((6986617863272729/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261063159803/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6980842898513553/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623918290976 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522126319606 : ℝ)) (s := (0.852868164710 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625861689242 : ℝ) ≤ 0.696198516939 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625861689242 : ℝ)) (Q := (0.625861689242 : ℝ))
      (s := (0.779934065123 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790129823619 : ℝ)) (R := (0.790665854877 : ℝ)) (Q2 := (0.625861689242 : ℝ)) (T := (0.834857983668 : ℝ))
    (B := ((6980842898513553/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520934740913/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1743768596459651/2500000000000000) := by
  have hk1 : kappa q ≤ 0.623113076777 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520934740913 : ℝ)) (s := (0.853596506384 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625055014519 : ℝ) ≤ 0.695619172338 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625055014519 : ℝ)) (Q := (0.625055014519 : ℝ))
      (s := (0.780580699752 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789620113709 : ℝ)) (R := (0.790156144967 : ℝ)) (Q2 := (0.625055014519 : ℝ)) (T := (0.834510546035 : ℝ))
    (B := ((1743768596459651/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25987158111/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742328078645151/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622308410584 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519743162220 : ℝ)) (s := (0.854322565151 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624248888443 : ℝ) ≤ 0.695040502403 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624248888443 : ℝ)) (Q := (0.624248888443 : ℝ))
      (s := (0.781225527795 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789110421792 : ℝ)) (R := (0.789646453050 : ℝ)) (Q2 := (0.624248888443 : ℝ)) (T := (0.834163368546 : ℝ))
    (B := ((1742328078645151/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518551583527/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6963556674114179/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621504291754 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518551583527 : ℝ)) (s := (0.855046346827 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623443310368 : ℝ) ≤ 0.694462505860 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623443310368 : ℝ)) (Q := (0.623443310368 : ℝ))
      (s := (0.781868555934 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788600747495 : ℝ)) (R := (0.789136778753 : ℝ)) (Q2 := (0.623443310368 : ℝ)) (T := (0.833816450762 : ℝ))
    (B := ((6963556674114179/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258680002417/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6957807453855597/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620700719647 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517360004834 : ℝ)) (s := (0.855767857190 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622638279657 : ℝ) ≤ 0.693885181442 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622638279657 : ℝ)) (Q := (0.622638279657 : ℝ))
      (s := (0.782509790806 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788091090448 : ℝ)) (R := (0.788627121706 : ℝ)) (Q2 := (0.622638279657 : ℝ)) (T := (0.833469792244 : ℝ))
    (B := ((6957807453855597/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516168426141/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952064643262509/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619897693626 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516168426141 : ℝ)) (s := (0.856487101979 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621833795669 : ℝ) ≤ 0.693308527880 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621833795669 : ℝ)) (Q := (0.621833795669 : ℝ))
      (s := (0.783149239012 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787581450278 : ℝ)) (R := (0.788117481536 : ℝ)) (Q2 := (0.621833795669 : ℝ)) (T := (0.833123392556 : ℝ))
    (B := ((6952064643262509/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64372105931/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (217072757244803/312500000000000) := by
  have hk1 : kappa q ≤ 0.619095213058 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514976847448 : ℝ)) (s := (0.857204086897 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621029857770 : ℝ) ≤ 0.692732543915 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621029857770 : ℝ)) (Q := (0.621029857770 : ℝ))
      (s := (0.783786907111 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787071826617 : ℝ)) (R := (0.787607857875 : ℝ)) (Q2 := (0.621029857770 : ℝ)) (T := (0.832777251262 : ℝ))
    (B := ((217072757244803/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102757053751/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (433787388069301/625000000000000) := by
  have hk1 : kappa q ≤ 0.618293277313 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513785268755 : ℝ)) (s := (0.857918817611 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620226465330 : ℝ) ≤ 0.692157228288 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620226465330 : ℝ)) (Q := (0.620226465330 : ℝ))
      (s := (0.784422801622 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786562219096 : ℝ)) (R := (0.787098250354 : ℝ)) (Q2 := (0.620226465330 : ℝ)) (T := (0.832431367928 : ℝ))
    (B := ((433787388069301/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256296845031/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6934874564668147/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617491885762 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512593690062 : ℝ)) (s := (0.858631299749 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619423617717 : ℝ) ≤ 0.691582579746 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619423617717 : ℝ)) (Q := (0.619423617717 : ℝ))
      (s := (0.785056929028 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786052627346 : ℝ)) (R := (0.786588658604 : ℝ)) (Q2 := (0.619423617717 : ℝ)) (T := (0.832085742123 : ℝ))
    (B := ((6934874564668147/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511402111369/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929157288132343/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616691037782 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511402111369 : ℝ)) (s := (0.859341538905 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618621314310 : ℝ) ≤ 0.691008597041 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618621314310 : ℝ)) (Q := (0.618621314310 : ℝ))
      (s := (0.785689295767 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785543051002 : ℝ)) (R := (0.786079082260 : ℝ)) (Q2 := (0.618621314310 : ℝ)) (T := (0.831740373415 : ℝ))
    (B := ((6929157288132343/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127552633169/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923446369162187/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615890732751 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510210532676 : ℝ)) (s := (0.860049540635 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617819554484 : ℝ) ≤ 0.690435278927 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617819554484 : ℝ)) (Q := (0.617819554484 : ℝ))
      (s := (0.786319908242 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785033489698 : ℝ)) (R := (0.785569520956 : ℝ)) (Q2 := (0.617819554484 : ℝ)) (T := (0.831395261376 : ℝ))
    (B := ((6923446369162187/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509018953983/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6917741797458341/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615090970051 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509018953983 : ℝ)) (s := (0.860755310461 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617018337619 : ℝ) ≤ 0.689862624162 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617018337619 : ℝ)) (Q := (0.617018337619 : ℝ))
      (s := (0.786948772820 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784523943068 : ℝ)) (R := (0.785059974326 : ℝ)) (Q2 := (0.617018337619 : ℝ)) (T := (0.831050405576 : ℝ))
    (B := ((6917741797458341/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50782737529/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912043562761109/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614291749067 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507827375290 : ℝ)) (s := (0.861458853868 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616217663100 : ℝ) ≤ 0.689290631511 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616217663100 : ℝ)) (Q := (0.616217663100 : ℝ))
      (s := (0.787575895825 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784014410750 : ℝ)) (R := (0.784550442008 : ℝ)) (Q2 := (0.616217663100 : ℝ)) (T := (0.830705805592 : ℝ))
    (B := ((6912043562761109/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (506635796597/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906351654850193/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613493069186 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506635796597 : ℝ)) (s := (0.862160176306 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615417530313 : ℝ) ≤ 0.688719299739 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615417530313 : ℝ)) (Q := (0.615417530313 : ℝ))
      (s := (0.788201283546 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783504892379 : ℝ)) (R := (0.784040923637 : ℝ)) (Q2 := (0.615417530313 : ℝ)) (T := (0.830361460996 : ℝ))
    (B := ((6906351654850193/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31590263619/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (862583257943057/1250000000000000) := by
  have hk1 : kappa q ≤ 0.612694929800 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505444217904 : ℝ)) (s := (0.862859283191 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614617938649 : ℝ) ≤ 0.688148627619 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614617938649 : ℝ)) (Q := (0.614617938649 : ℝ))
      (s := (0.788824942235 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782995387596 : ℝ)) (R := (0.783531418854 : ℝ)) (Q2 := (0.614617938649 : ℝ)) (T := (0.830017371367 : ℝ))
    (B := ((862583257943057/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504252639211/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1378997355740337/2000000000000000) := by
  have hk1 : kappa q ≤ 0.611897330303 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504252639211 : ℝ)) (s := (0.863556179904 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613818887499 : ℝ) ≤ 0.687578613926 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613818887499 : ℝ)) (Q := (0.613818887499 : ℝ))
      (s := (0.789446878105 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782485896038 : ℝ)) (R := (0.783021927296 : ℝ)) (Q2 := (0.613818887499 : ℝ)) (T := (0.829673536283 : ℝ))
    (B := ((1378997355740337/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (251530530259/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6889313790218353/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611100270092 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503061060518 : ℝ)) (s := (0.864250871791 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613020376263 : ℝ) ≤ 0.687009257441 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613020376263 : ℝ)) (Q := (0.613020376263 : ℝ))
      (s := (0.790067097332 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781976417348 : ℝ)) (R := (0.782512448606 : ℝ)) (Q2 := (0.613020376263 : ℝ)) (T := (0.829329955324 : ℝ))
    (B := ((6889313790218353/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20074779273/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883647088029393/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610303748568 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501869481825 : ℝ)) (s := (0.864943364165 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612222404338 : ℝ) ≤ 0.686440556948 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612222404338 : ℝ)) (Q := (0.612222404338 : ℝ))
      (s := (0.790685606058 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781466951166 : ℝ)) (R := (0.782002982424 : ℝ)) (Q2 := (0.612222404338 : ℝ)) (T := (0.828986628073 : ℝ))
    (B := ((6883647088029393/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125169475783/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3438993331053981/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609507765134 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500677903132 : ℝ)) (s := (0.865633662305 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611424971125 : ℝ) ≤ 0.685872511233 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611424971125 : ℝ)) (Q := (0.611424971125 : ℝ))
      (s := (0.791302410388 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780957497134 : ℝ)) (R := (0.781493528392 : ℝ)) (Q2 := (0.611424971125 : ℝ)) (T := (0.828643554111 : ℝ))
    (B := ((3438993331053981/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499486324439/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1374466500493043/2000000000000000) := by
  have hk1 : kappa q ≤ 0.608712319196 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499486324439 : ℝ)) (s := (0.866321771456 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610628076032 : ℝ) ≤ 0.685305119090 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610628076032 : ℝ)) (Q := (0.610628076032 : ℝ))
      (s := (0.791917516388 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780448054897 : ℝ)) (R := (0.780984086155 : ℝ)) (Q2 := (0.610628076032 : ℝ)) (T := (0.828300733024 : ℝ))
    (B := ((1374466500493043/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249147372873/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1716671149787519/2500000000000000) := by
  have hk1 : kappa q ≤ 0.607917410165 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498294745746 : ℝ)) (s := (0.867007696830 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609831718467 : ℝ) ≤ 0.684738379317 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609831718467 : ℝ)) (Q := (0.609831718467 : ℝ))
      (s := (0.792530930092 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779938624099 : ℝ)) (R := (0.780474655357 : ℝ)) (Q2 := (0.609831718467 : ℝ)) (T := (0.827958164401 : ℝ))
    (B := ((1716671149787519/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497103167053/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430521471124509/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607123037453 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497103167053 : ℝ)) (s := (0.867691443606 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609035897841 : ℝ) ≤ 0.684172290712 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609035897841 : ℝ)) (Q := (0.609035897841 : ℝ))
      (s := (0.793142657497 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779429204386 : ℝ)) (R := (0.779965235644 : ℝ)) (Q2 := (0.609035897841 : ℝ)) (T := (0.827615847826 : ℝ))
    (B := ((3430521471124509/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12397789709/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (856925940235729/1250000000000000) := by
  have hk1 : kappa q ≤ 0.606329200475 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495911588360 : ℝ)) (s := (0.868373016929 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608240613568 : ℝ) ≤ 0.683606852082 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608240613568 : ℝ)) (Q := (0.608240613568 : ℝ))
      (s := (0.793752704567 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778919795403 : ℝ)) (R := (0.779455826661 : ℝ)) (Q2 := (0.608240613568 : ℝ)) (T := (0.827273782891 : ℝ))
    (B := ((856925940235729/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494720009667/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (856222291027677/1250000000000000) := by
  have hk1 : kappa q ≤ 0.605535898652 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494720009667 : ℝ)) (s := (0.869052421915 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607445865068 : ℝ) ≤ 0.683042062236 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607445865068 : ℝ)) (Q := (0.607445865068 : ℝ))
      (s := (0.794361077227 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778410396801 : ℝ)) (R := (0.778946428059 : ℝ)) (Q2 := (0.607445865068 : ℝ)) (T := (0.826931969189 : ℝ))
    (B := ((856222291027677/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246764215487/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422077675726773/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604743131404 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493528430974 : ℝ)) (s := (0.869729663643 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606651651762 : ℝ) ≤ 0.682477919987 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606651651762 : ℝ)) (Q := (0.606651651762 : ℝ))
      (s := (0.794967781369 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777901008227 : ℝ)) (R := (0.778437039485 : ℝ)) (Q2 := (0.606651651762 : ℝ)) (T := (0.826590406310 : ℝ))
    (B := ((3422077675726773/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492336852281/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419269290908333/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603950898157 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492336852281 : ℝ)) (s := (0.870404747165 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605857973072 : ℝ) ≤ 0.681914424154 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605857973072 : ℝ)) (Q := (0.605857973072 : ℝ))
      (s := (0.795572822855 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777391629331 : ℝ)) (R := (0.777927660589 : ℝ)) (Q2 := (0.605857973072 : ℝ)) (T := (0.826249093852 : ℝ))
    (B := ((3419269290908333/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122786318397/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (683292800958167/1000000000000000) := by
  have hk1 : kappa q ≤ 0.603159198339 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491145273588 : ℝ)) (s := (0.871077677497 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605064828425 : ℝ) ≤ 0.681351573557 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605064828425 : ℝ)) (Q := (0.605064828425 : ℝ))
      (s := (0.796176207509 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776882259763 : ℝ)) (R := (0.777418291021 : ℝ)) (Q2 := (0.605064828425 : ℝ)) (T := (0.825908031408 : ℝ))
    (B := ((683292800958167/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97990738979/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1365464725011137/2000000000000000) := by
  have hk1 : kappa q ≤ 0.602368031382 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489953694895 : ℝ)) (s := (0.871748459626 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604272217255 : ℝ) ≤ 0.680789367024 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604272217255 : ℝ)) (Q := (0.604272217255 : ℝ))
      (s := (0.796777941119 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776372899178 : ℝ)) (R := (0.776908930436 : ℝ)) (Q2 := (0.604272217255 : ℝ)) (T := (0.825567218580 : ℝ))
    (B := ((1365464725011137/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244381058101/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821725418581867/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601577396719 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488762116202 : ℝ)) (s := (0.872417098507 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603480138992 : ℝ) ≤ 0.680227803386 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603480138992 : ℝ)) (Q := (0.603480138992 : ℝ))
      (s := (0.797378029446 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775863547227 : ℝ)) (R := (0.776399578485 : ℝ)) (Q2 := (0.603480138992 : ℝ)) (T := (0.825226654966 : ℝ))
    (B := ((6821725418581867/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487570537509/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816133380539181/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600787293789 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487570537509 : ℝ)) (s := (0.873083599064 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602688593072 : ℝ) ≤ 0.679666881475 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602688593072 : ℝ)) (Q := (0.602688593072 : ℝ))
      (s := (0.797976478213 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775354203564 : ℝ)) (R := (0.775890234822 : ℝ)) (Q2 := (0.602688593072 : ℝ)) (T := (0.824886340166 : ℝ))
    (B := ((6816133380539181/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15199342463/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810547501342201/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599997722031 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486378958816 : ℝ)) (s := (0.873747966190 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601897578937 : ℝ) ≤ 0.679106600133 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601897578937 : ℝ)) (Q := (0.601897578937 : ℝ))
      (s := (0.798573293111 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774844867846 : ℝ)) (R := (0.775380899104 : ℝ)) (Q2 := (0.601897578937 : ℝ)) (T := (0.824546273786 : ℝ))
    (B := ((6810547501342201/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485187380123/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402483885720449/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599208680890 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485187380123 : ℝ)) (s := (0.874410204750 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601107096029 : ℝ) ≤ 0.678546958202 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601107096029 : ℝ)) (Q := (0.601107096029 : ℝ))
      (s := (0.799168479799 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774335539728 : ℝ)) (R := (0.774871570986 : ℝ)) (Q2 := (0.601107096029 : ℝ)) (T := (0.824206455430 : ℝ))
    (B := ((3402483885720449/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48399580143/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799394181320437/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598420169812 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483995801430 : ℝ)) (s := (0.875070319574 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600317143792 : ℝ) ≤ 0.677987954529 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600317143792 : ℝ)) (Q := (0.600317143792 : ℝ))
      (s := (0.799762043904 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773826218868 : ℝ)) (R := (0.774362250126 : ℝ)) (Q2 := (0.600317143792 : ℝ)) (T := (0.823866884705 : ℝ))
    (B := ((6799394181320437/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482804222737/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (271753068860039/400000000000000) := by
  have hk1 : kappa q ≤ 0.597632188246 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482804222737 : ℝ)) (s := (0.875728315466 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599527721677 : ℝ) ≤ 0.677429587967 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599527721677 : ℝ)) (Q := (0.599527721677 : ℝ))
      (s := (0.800353991020 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773316904925 : ℝ)) (R := (0.773852936183 : ℝ)) (Q2 := (0.599527721677 : ℝ)) (T := (0.823527561218 : ℝ))
    (B := ((271753068860039/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120403161011/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (848533092503777/1250000000000000) := by
  have hk1 : kappa q ≤ 0.596844735646 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481612644044 : ℝ)) (s := (0.876384197198 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598738829133 : ℝ) ≤ 0.676871857369 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598738829133 : ℝ)) (Q := (0.598738829133 : ℝ))
      (s := (0.800944326710 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772807597557 : ℝ)) (R := (0.773343628815 : ℝ)) (Q2 := (0.598738829133 : ℝ)) (T := (0.823188484579 : ℝ))
    (B := ((848533092503777/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480421065351/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1695677091032967/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596057811467 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480421065351 : ℝ)) (s := (0.877037969513 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597950465617 : ℝ) ≤ 0.676314761599 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597950465617 : ℝ)) (Q := (0.597950465617 : ℝ))
      (s := (0.801533056504 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772298296426 : ℝ)) (R := (0.772834327684 : ℝ)) (Q2 := (0.597950465617 : ℝ)) (T := (0.822849654402 : ℝ))
    (B := ((1695677091032967/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (239614743329/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777158092818157/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595271415168 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479229486658 : ℝ)) (s := (0.877689637126 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597162630587 : ℝ) ≤ 0.675758299520 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597162630587 : ℝ)) (Q := (0.597162630587 : ℝ))
      (s := (0.802120185902 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771789001194 : ℝ)) (R := (0.772325032452 : ℝ)) (Q2 := (0.597162630587 : ℝ)) (T := (0.822511070300 : ℝ))
    (B := ((6777158092818157/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12925 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (95607581593/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1692903479185391/2500000000000000) := by
  have hk1 : kappa q ≤ 0.594485546211 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478037907965 : ℝ)) (s := (0.878339204721 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596375323503 : ℝ) ≤ 0.675202470001 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596375323503 : ℝ)) (Q := (0.596375323503 : ℝ))
      (s := (0.802705720372 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771279711523 : ℝ)) (R := (0.771815742781 : ℝ)) (Q2 := (0.596375323503 : ℝ)) (T := (0.822172731887 : ℝ))
    (B := ((1692903479185391/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S23
namespace BstLean.Part269.S23
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12925 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052020548636 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S23.wn_upper (by omega : 12925 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010504501753 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035493437527)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010504501753 + 2 * 0.737676 / 12925) := by gcongr
    _ ≤ (0.052020548636 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12925 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12925 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.688170009020 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.688170009020 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12925 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003284487036 + 0.003234353889 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003284487036 + 0.003234353889 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.688170009020 ≤ R)
    (hB : (X + 0.052020548636 + R + 0.008406961539) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008406961539 := by
    convert (BstLean.Part269.S23.finite_centre_upper (by omega : 12925 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (84795089207/1000000000000)
  | 2 => (17145147971/200000000000)
  | 3 => (86652876103/1000000000000)
  | 4 => (2736797741/31250000000)
  | 5 => (11062618977/125000000000)
  | 6 => (89424668143/1000000000000)
  | 7 => (2823453057/31250000000)
  | 8 => (18256121177/200000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003284487036 + 0.003234353889 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218485534910 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010870677913 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003284487036 + 0.003234353889 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220059535139 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010984640121 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003284487036 + 0.003234353889 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221612928425 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011098225922 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003284487036 + 0.003234353889 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223145927177 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011211443567 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003284487036 + 0.003234353889 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224658738381 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011324301071 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003284487036 + 0.003234353889 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226151562117 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011436806102 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003284487036 + 0.003234353889 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227624593452 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011548966121 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12925 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003284487036 + 0.003234353889 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229078020991 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011660788269 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12925 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g) :
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

end BstLean.Part269.S23

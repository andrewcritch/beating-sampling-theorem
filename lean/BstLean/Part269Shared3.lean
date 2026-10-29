import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S3
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12425 ≤ n) : wn n ≤ 1.036206835911 := by
  have hnR : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.467484048039 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.467484048039 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036206835911 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12425 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12425 + 24 / (12425 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12425 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008575175562 : ℝ) := by
  have hnR : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.467484048039 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12425 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036206835911 * (81 / 1000 / 12425)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036206835911 * n *
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
        4 * (1 / 2.506628) * 1.036206835911 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036206835911 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036206835911 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12425)) / 111.467484048039 := by gcongr
    _ ≤ (0.008575175562 : ℝ) := by norm_num

end BstLean.Part269.S3
namespace BstLean.Part269.S3
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12425 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12425 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12425 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12425 + 0.008575175562 / 111.467484048039) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12425 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12425 := by gcongr
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
  have hn : (111.467484048039 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S3.finite_centre_upper (by omega : 12425 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105606136131/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1402156699107419/2000000000000000) := by
  have hk1 : kappa q ≤ 0.627916294649 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528030680655 : ℝ)) (s := (0.849225294188 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629916793981 : ℝ) ≤ 0.699115111002 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629916793981 : ℝ)) (Q := (0.629916793981 : ℝ))
      (s := (0.776662624736 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792665572065 : ℝ)) (R := (0.793223173997 : ℝ)) (Q2 := (0.629916793981 : ℝ)) (T := (0.836604897029 : ℝ))
    (B := ((1402156699107419/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (6585421859/12500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004955777565837/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627104726979 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526833748720 : ℝ)) (s := (0.849968353064 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629103733909 : ℝ) ≤ 0.698529754648 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629103733909 : ℝ)) (Q := (0.629103733909 : ℝ))
      (s := (0.777321356958 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792153483529 : ℝ)) (R := (0.792711085461 : ℝ)) (Q2 := (0.629103733909 : ℝ)) (T := (0.836254586662 : ℝ))
    (B := ((7004955777565837/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105127363357/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3499567307027731/5000000000000000) := by
  have hk1 : kappa q ≤ 0.626293715506 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525636816785 : ℝ)) (s := (0.850709078852 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628291230687 : ℝ) ≤ 0.697945085500 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628291230687 : ℝ)) (Q := (0.628291230687 : ℝ))
      (s := (0.777978231985 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791641415032 : ℝ)) (R := (0.792199016964 : ℝ)) (Q2 := (0.628291230687 : ℝ)) (T := (0.835904541009 : ℝ))
    (B := ((3499567307027731/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524439884851/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6993319994020611/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625483259564 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524439884851 : ℝ)) (s := (0.851447477639 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627479283648 : ℝ) ≤ 0.697361102248 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627479283648 : ℝ)) (Q := (0.627479283648 : ℝ))
      (s := (0.778633256799 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791129366192 : ℝ)) (R := (0.791686968124 : ℝ)) (Q2 := (0.627479283648 : ℝ)) (T := (0.835554759617 : ℝ))
    (B := ((6993319994020611/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130810738229/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (873438988314959/1250000000000000) := by
  have hk1 : kappa q ≤ 0.624673358488 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523242952916 : ℝ)) (s := (0.852183555477 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667892126 : ℝ) ≤ 0.696777803584 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667892126 : ℝ)) (Q := (0.626667892126 : ℝ))
      (s := (0.779286438339 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790617336627 : ℝ)) (R := (0.791174938559 : ℝ)) (Q2 := (0.626667892126 : ℝ)) (T := (0.835205242035 : ℝ))
    (B := ((873438988314959/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261023010491/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981710340654507/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623864011618 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522046020982 : ℝ)) (s := (0.852917318371 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625857055461 : ℝ) ≤ 0.696195188207 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625857055461 : ℝ)) (Q := (0.625857055461 : ℝ))
      (s := (0.779937783500 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790105325957 : ℝ)) (R := (0.790662927889 : ℝ)) (Q2 := (0.625857055461 : ℝ)) (T := (0.834855987814 : ℝ))
    (B := ((6981710340654507/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520849089047/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975915285570177/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623055218296 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520849089047 : ℝ)) (s := (0.853648772294 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625046772991 : ℝ) ≤ 0.695613254816 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625046772991 : ℝ)) (Q := (0.625046772991 : ℝ))
      (s := (0.780587299137 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789593333801 : ℝ)) (R := (0.790150935733 : ℝ)) (Q2 := (0.625046772991 : ℝ)) (T := (0.834506996503 : ℝ))
    (B := ((6975915285570177/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519652157113/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742531682613667/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622246977869 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519652157113 : ℝ)) (s := (0.854377923175 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624237044065 : ℝ) ≤ 0.695032002119 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624237044065 : ℝ)) (Q := (0.624237044065 : ℝ))
      (s := (0.781234992059 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789081359783 : ℝ)) (R := (0.789638961715 : ℝ)) (Q2 := (0.624237044065 : ℝ)) (T := (0.834158267659 : ℝ))
    (B := ((1742531682613667/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259227612589/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964344664538629/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621439289683 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518455225178 : ℝ)) (s := (0.855104776905 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623427868026 : ℝ) ≤ 0.694451428822 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623427868026 : ℝ)) (Q := (0.623427868026 : ℝ))
      (s := (0.781880869039 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788569403522 : ℝ)) (R := (0.789127005454 : ℝ)) (Q2 := (0.623427868026 : ℝ)) (T := (0.833809800832 : ℝ))
    (B := ((6964344664538629/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517258293243/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3479284538547551/5000000000000000) := by
  have hk1 : kappa q ≤ 0.620632153093 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517258293243 : ℝ)) (s := (0.855829339338 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622619244228 : ℝ) ≤ 0.693871533641 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622619244228 : ℝ)) (Q := (0.622619244228 : ℝ))
      (s := (0.782524936802 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788057464644 : ℝ)) (R := (0.788615066576 : ℝ)) (Q2 := (0.622619244228 : ℝ)) (T := (0.833461595581 : ℝ))
    (B := ((3479284538547551/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516061361309/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (869099994679907/1250000000000000) := by
  have hk1 : kappa q ≤ 0.619825567452 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516061361309 : ℝ)) (s := (0.856551616288 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621811172022 : ℝ) ≤ 0.693292315292 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621811172022 : ℝ)) (Q := (0.621811172022 : ℝ))
      (s := (0.783167202039 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787545542772 : ℝ)) (R := (0.788103144704 : ℝ)) (Q2 := (0.621811172022 : ℝ)) (T := (0.833113651463 : ℝ))
    (B := ((869099994679907/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257432214687/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (694703729492813/1000000000000000) := by
  have hk1 : kappa q ≤ 0.619019532119 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514864429374 : ℝ)) (s := (0.857271613531 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621003650768 : ℝ) ≤ 0.692713772499 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621003650768 : ℝ)) (Q := (0.621003650768 : ℝ))
      (s := (0.783807671392 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787033637532 : ℝ)) (R := (0.787591239464 : ℝ)) (Q2 := (0.621003650768 : ℝ)) (T := (0.832765968037 : ℝ))
    (B := ((694703729492813/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (3210421859/6250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (694128107896037/1000000000000000) := by
  have hk1 : kappa q ≤ 0.618214046454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513667497440 : ℝ)) (s := (0.857989336807 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620196679823 : ℝ) ≤ 0.692135903984 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620196679823 : ℝ)) (Q := (0.620196679823 : ℝ))
      (s := (0.784446351472 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786521748550 : ℝ)) (R := (0.787079350482 : ℝ)) (Q2 := (0.620196679823 : ℝ)) (T := (0.832418544862 : ℝ))
    (B := ((694128107896037/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102494113101/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935531298975973/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617409109823 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512470565505 : ℝ)) (s := (0.858704791818 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619390258553 : ℝ) ≤ 0.691558708481 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619390258553 : ℝ)) (Q := (0.619390258553 : ℝ))
      (s := (0.785083248841 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786009875454 : ℝ)) (R := (0.786567477386 : ℝ)) (Q2 := (0.619390258553 : ℝ)) (T := (0.832071381502 : ℝ))
    (B := ((6935531298975973/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51127363357/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929787944456033/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616604721591 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511273633570 : ℝ)) (s := (0.859417984229 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618584386322 : ℝ) ≤ 0.690982184721 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618584386322 : ℝ)) (Q := (0.618584386322 : ℝ))
      (s := (0.785718370028 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785498017871 : ℝ)) (R := (0.786055619803 : ℝ)) (Q2 := (0.618584386322 : ℝ)) (T := (0.831724477518 : ℝ))
    (B := ((6929787944456033/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127519175409/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (692405100492249/1000000000000000) := by
  have hk1 : kappa q ≤ 0.615800881132 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510076701636 : ℝ)) (s := (0.860128919668 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617779062500 : ℝ) ≤ 0.690406331443 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617779062500 : ℝ)) (Q := (0.617779062500 : ℝ))
      (s := (0.786351721520 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784986175432 : ℝ)) (R := (0.785543777364 : ℝ)) (Q2 := (0.617779062500 : ℝ)) (T := (0.831377832477 : ℝ))
    (B := ((692405100492249/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508879769701/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (55346563759503/80000000000000) := by
  have hk1 : kappa q ≤ 0.614997587817 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508879769701 : ℝ)) (s := (0.860837603727 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616974286461 : ℝ) ≤ 0.689831147392 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616974286461 : ℝ)) (Q := (0.616974286461 : ℝ))
      (s := (0.786983309764 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784474347767 : ℝ)) (R := (0.785031949699 : ℝ)) (Q2 := (0.616974286461 : ℝ)) (T := (0.831031445946 : ℝ))
    (B := ((55346563759503/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507682837767/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (864074541138133/1250000000000000) := by
  have hk1 : kappa q ≤ 0.614194841024 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507682837767 : ℝ)) (s := (0.861544041961 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616170057581 : ℝ) ≤ 0.689256631313 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616170057581 : ℝ)) (Q := (0.616170057581 : ℝ))
      (s := (0.787613141169 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783962534508 : ℝ)) (R := (0.784520136440 : ℝ)) (Q2 := (0.616170057581 : ℝ)) (T := (0.830685317492 : ℝ))
    (B := ((864074541138133/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63310738229/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1381375714413407/2000000000000000) := by
  have hk1 : kappa q ≤ 0.613392640132 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506485905832 : ℝ)) (s := (0.862248239891 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615366375236 : ℝ) ≤ 0.688682781957 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615366375236 : ℝ)) (Q := (0.615366375236 : ℝ))
      (s := (0.788241222108 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783450735286 : ℝ)) (R := (0.784008337218 : ℝ)) (Q2 := (0.615366375236 : ℝ)) (T := (0.830339446686 : ℝ))
    (B := ((1381375714413407/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505288973897/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6901167188506619/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612590984526 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505288973897 : ℝ)) (s := (0.862950203001 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614563238810 : ℝ) ≤ 0.688109598078 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614563238810 : ℝ)) (Q := (0.614563238810 : ℝ))
      (s := (0.788867558912 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782938949736 : ℝ)) (R := (0.783496551668 : ℝ)) (Q2 := (0.614563238810 : ℝ)) (T := (0.829993833097 : ℝ))
    (B := ((6901167188506619/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504092041963/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895462168146263/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611789873591 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504092041963 : ℝ)) (s := (0.863649936740 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613760647688 : ℝ) ≤ 0.687537078438 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613760647688 : ℝ)) (Q := (0.613760647688 : ℝ))
      (s := (0.789492157878 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782427177492 : ℝ)) (R := (0.782984779424 : ℝ)) (Q2 := (0.613760647688 : ℝ)) (T := (0.829648476300 : ℝ))
    (B := ((6895462168146263/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125723777507/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (861220437593473/1250000000000000) := by
  have hk1 : kappa q ≤ 0.610989306717 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502895110028 : ℝ)) (s := (0.864347446523 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612958601260 : ℝ) ≤ 0.686965221800 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612958601260 : ℝ)) (Q := (0.612958601260 : ℝ))
      (s := (0.790115025260 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781915418191 : ℝ)) (R := (0.782473020123 : ℝ)) (Q2 := (0.612958601260 : ℝ)) (T := (0.829303375870 : ℝ))
    (B := ((861220437593473/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250849089047/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3442035588056069/5000000000000000) := by
  have hk1 : kappa q ≤ 0.610189283297 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501698178094 : ℝ)) (s := (0.865042737729 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612157098916 : ℝ) ≤ 0.686394026933 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612157098916 : ℝ)) (Q := (0.612157098916 : ℝ))
      (s := (0.790736167282 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781403671469 : ℝ)) (R := (0.781961273401 : ℝ)) (Q2 := (0.612157098916 : ℝ)) (T := (0.828958531384 : ℝ))
    (B := ((3442035588056069/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500501246159/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439192592039591/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609389802726 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500501246159 : ℝ)) (s := (0.865735815705 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611356140050 : ℝ) ≤ 0.685823492606 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611356140050 : ℝ)) (Q := (0.611356140050 : ℝ))
      (s := (0.791355590126 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780891936963 : ℝ)) (R := (0.781449538895 : ℝ)) (Q2 := (0.611356140050 : ℝ)) (T := (0.828613942416 : ℝ))
    (B := ((3439192592039591/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19972172569/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872705514527437/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608590864404 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499304314225 : ℝ)) (s := (0.866426685760 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610555724061 : ℝ) ≤ 0.685253617599 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610555724061 : ℝ)) (Q := (0.610555724061 : ℝ))
      (s := (0.791973299940 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780380214313 : ℝ)) (R := (0.780937816245 : ℝ)) (Q2 := (0.610555724061 : ℝ)) (T := (0.828269608549 : ℝ))
    (B := ((6872705514527437/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49810738229/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6867032157373861/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607792467731 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498107382290 : ℝ)) (s := (0.867115353173 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609755850350 : ℝ) ≤ 0.684684400691 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609755850350 : ℝ)) (Q := (0.609755850350 : ℝ))
      (s := (0.792589302833 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779868503159 : ℝ)) (R := (0.780426105091 : ℝ)) (Q2 := (0.609755850350 : ℝ)) (T := (0.827925529363 : ℝ))
    (B := ((6867032157373861/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99382090071/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861365102573617/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606994612115 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496910450355 : ℝ)) (s := (0.867801823188 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608956518320 : ℝ) ≤ 0.684115840668 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608956518320 : ℝ)) (Q := (0.608956518320 : ℝ))
      (s := (0.793203604881 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779356803141 : ℝ)) (R := (0.779914405073 : ℝ)) (Q2 := (0.608956518320 : ℝ)) (T := (0.827581704442 : ℝ))
    (B := ((6861365102573617/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495713518421/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1371140868023969/2000000000000000) := by
  have hk1 : kappa q ≤ 0.606197296964 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495713518421 : ℝ)) (s := (0.868486101015 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608157727382 : ℝ) ≤ 0.683547936320 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608157727382 : ℝ)) (Q := (0.608157727382 : ℝ))
      (s := (0.793816212121 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778845113904 : ℝ)) (R := (0.779402715836 : ℝ)) (Q2 := (0.608157727382 : ℝ)) (T := (0.827238133369 : ℝ))
    (B := ((1371140868023969/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247258293243/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3425024930021719/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605400521687 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494516586486 : ℝ)) (s := (0.869168191831 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607359476940 : ℝ) ≤ 0.682980686439 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607359476940 : ℝ)) (Q := (0.607359476940 : ℝ))
      (s := (0.794427130561 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778333435087 : ℝ)) (R := (0.778891037019 : ℝ)) (Q2 := (0.607359476940 : ℝ)) (T := (0.826894815731 : ℝ))
    (B := ((3425024930021719/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61664956819/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (427775103275801/625000000000000) := by
  have hk1 : kappa q ≤ 0.604604285702 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493319654552 : ℝ)) (s := (0.869848100782 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606561766415 : ℝ) ≤ 0.682414089826 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606561766415 : ℝ)) (Q := (0.606561766415 : ℝ))
      (s := (0.795036366165 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777821766338 : ℝ)) (R := (0.778379368270 : ℝ)) (Q2 := (0.606561766415 : ℝ)) (T := (0.826551751116 : ℝ))
    (B := ((427775103275801/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492122722617/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (854844963416713/1250000000000000) := by
  have hk1 : kappa q ≤ 0.603808588425 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492122722617 : ℝ)) (s := (0.870525832980 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605764595219 : ℝ) ≤ 0.681848145281 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605764595219 : ℝ)) (Q := (0.605764595219 : ℝ))
      (s := (0.795643924868 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777310107301 : ℝ)) (R := (0.777867709233 : ℝ)) (Q2 := (0.605764595219 : ℝ)) (T := (0.826208939114 : ℝ))
    (B := ((854844963416713/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245462895341/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416562007474457/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603013429277 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490925790682 : ℝ)) (s := (0.871201393504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604967962774 : ℝ) ≤ 0.681282851612 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604967962774 : ℝ)) (Q := (0.604967962774 : ℝ))
      (s := (0.796249812570 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776798457623 : ℝ)) (R := (0.777356059555 : ℝ)) (Q2 := (0.604967962774 : ℝ)) (T := (0.825866379316 : ℝ))
    (B := ((3416562007474457/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (122432214687/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (10923991304701/16000000000000) := by
  have hk1 : kappa q ≤ 0.602218807683 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489728858748 : ℝ)) (s := (0.871874787404 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604171868501 : ℝ) ≤ 0.680718207628 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604171868501 : ℝ)) (Q := (0.604171868501 : ℝ))
      (s := (0.796854035136 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776286816950 : ℝ)) (R := (0.776844418882 : ℝ)) (Q2 := (0.604171868501 : ℝ)) (T := (0.825524071314 : ℝ))
    (B := ((10923991304701/16000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488531926813/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364374269803533/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601424723070 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488531926813 : ℝ)) (s := (0.872546019695 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603376311830 : ℝ) ≤ 0.680154212149 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603376311830 : ℝ)) (Q := (0.603376311830 : ℝ))
      (s := (0.797456598395 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775775184933 : ℝ)) (R := (0.776332786865 : ℝ)) (Q2 := (0.603376311830 : ℝ)) (T := (0.825182014705 : ℝ))
    (B := ((1364374269803533/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487334994879/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816254355940301/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600631174869 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487334994879 : ℝ)) (s := (0.873215095361 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602581292188 : ℝ) ≤ 0.679590863991 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602581292188 : ℝ)) (Q := (0.602581292188 : ℝ))
      (s := (0.798057508145 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775263561221 : ℝ)) (R := (0.775821163153 : ℝ)) (Q2 := (0.602581292188 : ℝ)) (T := (0.824840209084 : ℝ))
    (B := ((6816254355940301/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (15191814467/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810643576495019/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599838162512 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486138062944 : ℝ)) (s := (0.873882019358 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601786809007 : ℝ) ≤ 0.679028161978 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601786809007 : ℝ)) (Q := (0.601786809007 : ℝ))
      (s := (0.798656770150 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774751945464 : ℝ)) (R := (0.775309547396 : ℝ)) (Q2 := (0.601786809007 : ℝ)) (T := (0.824498654049 : ℝ))
    (B := ((6810643576495019/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484941131009/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402519500503411/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599045685437 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484941131009 : ℝ)) (s := (0.874546796608 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600992861722 : ℝ) ≤ 0.678466104938 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600992861722 : ℝ)) (Q := (0.600992861722 : ℝ))
      (s := (0.799254390141 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774240337314 : ℝ)) (R := (0.774797939246 : ℝ)) (Q2 := (0.600992861722 : ℝ)) (T := (0.824157349199 : ℝ))
    (B := ((3402519500503411/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19349767963/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799440619836511/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598253743083 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483744199075 : ℝ)) (s := (0.875209432000 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600199449775 : ℝ) ≤ 0.677904691707 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600199449775 : ℝ)) (Q := (0.600199449775 : ℝ))
      (s := (0.799850373814 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773728736426 : ℝ)) (R := (0.774286338358 : ℝ)) (Q2 := (0.600199449775 : ℝ)) (T := (0.823816294139 : ℝ))
    (B := ((6799440619836511/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24127363357/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1698462105845121/2500000000000000) := by
  have hk1 : kappa q ≤ 0.597462334894 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482547267140 : ℝ)) (s := (0.875869930399 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599406572605 : ℝ) ≤ 0.677343921119 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599406572605 : ℝ)) (Q := (0.599406572605 : ℝ))
      (s := (0.800444726835 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773217142452 : ℝ)) (R := (0.773774744384 : ℝ)) (Q2 := (0.599406572605 : ℝ)) (T := (0.823475488470 : ℝ))
    (B := ((1698462105845121/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240675167603/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788262402070527/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596671460315 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481350335206 : ℝ)) (s := (0.876528296633 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598614229658 : ℝ) ≤ 0.676783792016 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598614229658 : ℝ)) (Q := (0.598614229658 : ℝ))
      (s := (0.801037454837 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772705555048 : ℝ)) (R := (0.773263156980 : ℝ)) (Q2 := (0.598614229658 : ℝ)) (T := (0.823134931797 : ℝ))
    (B := ((6788262402070527/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480153403271/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782681766125129/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595881118794 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480153403271 : ℝ)) (s := (0.877184535504 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597822420381 : ℝ) ≤ 0.676224303243 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597822420381 : ℝ)) (Q := (0.597822420381 : ℝ))
      (s := (0.801628563420 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772193973870 : ℝ)) (R := (0.772751575802 : ℝ)) (Q2 := (0.597822420381 : ℝ)) (T := (0.822794623727 : ℝ))
    (B := ((6782681766125129/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478956471337/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1355421369724189/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595091309787 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478956471337 : ℝ)) (s := (0.877838651784 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597031144229 : ℝ) ≤ 0.675665453652 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597031144229 : ℝ)) (Q := (0.597031144229 : ℝ))
      (s := (0.802218058150 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771682398578 : ℝ)) (R := (0.772240000510 : ℝ)) (Q2 := (0.597031144229 : ℝ)) (T := (0.822454563870 : ℝ))
    (B := ((1355421369724189/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12425 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (238879769701/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (169288452011167/250000000000000) := by
  have hk1 : kappa q ≤ 0.594302032745 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477759539402 : ℝ)) (s := (0.878490650213 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596240400651 : ℝ) ≤ 0.675107242095 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596240400651 : ℝ)) (Q := (0.596240400651 : ℝ))
      (s := (0.802805944567 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771170828826 : ℝ)) (R := (0.771728430758 : ℝ)) (Q2 := (0.596240400651 : ℝ)) (T := (0.822114751835 : ℝ))
    (B := ((169288452011167/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S3
namespace BstLean.Part269.S3
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12425 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.053068278929 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S3.wn_upper (by omega : 12425 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010713775334 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036206835911)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010713775334 + 2 * 0.737676 / 12425) := by gcongr
    _ ≤ (0.053068278929 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12425 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12425 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.467484048039 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12425 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.467484048039 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12425 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.004185346396 + 0.003369149079 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004185346396 + 0.003369149079 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.467484048039 ≤ R)
    (hB : (X + 0.053068278929 + R + 0.008575175562) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008575175562 := by
    convert (BstLean.Part269.S3.finite_centre_upper (by omega : 12425 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (21564883859/250000000000)
  | 2 => (43608650179/500000000000)
  | 3 => (88175534431/1000000000000)
  | 4 => (44568090763/500000000000)
  | 5 => (5631348351/62500000000)
  | 6 => (91074485861/1000000000000)
  | 7 => (23014549101/250000000000)
  | 8 => (9305655087/100000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.004185346396 + 0.003369149079 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.220682428513 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011087246556 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.004185346396 + 0.003369149079 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.222243052459 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011203479152 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.004185346396 + 0.003369149079 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.223783456665 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011319327840 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.004185346396 + 0.003369149079 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.225303840000 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011434801038 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.004185346396 + 0.003369149079 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.226804396573 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011549906920 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.004185346396 + 0.003369149079 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.228285314229 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011664653308 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.004185346396 + 0.003369149079 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.229746776387 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011779047810 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12425 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.004185346396 + 0.003369149079 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.231188960567 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011893097709 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12425 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g) :
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

end BstLean.Part269.S3

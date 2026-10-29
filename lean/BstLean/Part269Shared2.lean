import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S2
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12400 ≤ n) : wn n ≤ 1.036243641051 := by
  have hnR : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.355287256600 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.355287256600 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036243641051 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12400 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12400 + 24 / (12400 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12400 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008583853148 : ℝ) := by
  have hnR : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.355287256600 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12400 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036243641051 * (81 / 1000 / 12400)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036243641051 * n *
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
        4 * (1 / 2.506628) * 1.036243641051 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036243641051 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036243641051 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12400)) / 111.355287256600 := by gcongr
    _ ≤ (0.008583853148 : ℝ) := by norm_num

end BstLean.Part269.S2
namespace BstLean.Part269.S2
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12400 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12400 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12400 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12400 + 0.008583853148 / 111.355287256600) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12400 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12400 := by gcongr
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
  have hn : (111.355287256600 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S2.finite_centre_upper (by omega : 12400 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528027917757/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (876354474686193/1250000000000000) := by
  have hk1 : kappa q ≤ 0.627914420653 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528027917757 : ℝ)) (s := (0.849227012094 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629917514853 : ℝ) ≤ 0.699115630116 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629917514853 : ℝ)) (Q := (0.629917514853 : ℝ))
      (s := (0.776662040068 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792664901746 : ℝ)) (R := (0.793223627876 : ℝ)) (Q2 := (0.629917514853 : ℝ)) (T := (0.836605207631 : ℝ))
    (B := ((876354474686193/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131707677383/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7005006693661773/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627102666996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526830709532 : ℝ)) (s := (0.849970236829 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629104267298 : ℝ) ≤ 0.698530138563 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629104267298 : ℝ)) (Q := (0.629104267298 : ℝ))
      (s := (0.777320925274 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792152695383 : ℝ)) (R := (0.792711421513 : ℝ)) (Q2 := (0.629104267298 : ℝ)) (T := (0.836254816467 : ℝ))
    (B := ((7005006693661773/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131408375327/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6999184147362767/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626291469793 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525633501308 : ℝ)) (s := (0.850711127413 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628291576852 : ℝ) ≤ 0.697945334536 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628291576852 : ℝ)) (Q := (0.628291576852 : ℝ))
      (s := (0.777977952424 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791640509070 : ℝ)) (R := (0.792199235200 : ℝ)) (Q2 := (0.628291576852 : ℝ)) (T := (0.835904690140 : ℝ))
    (B := ((6999184147362767/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131109073271/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496684073799749/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625480828374 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524436293084 : ℝ)) (s := (0.851449689939 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627479442842 : ℝ) ≤ 0.697361216718 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627479442842 : ℝ)) (Q := (0.627479442842 : ℝ))
      (s := (0.778633128509 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791128342421 : ℝ)) (R := (0.791687068551 : ℝ)) (Q2 := (0.627479442842 : ℝ)) (T := (0.835554828194 : ℝ))
    (B := ((3496684073799749/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523239084859/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987558683422727/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624670742075 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523239084859 : ℝ)) (s := (0.852185930462 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626667864602 : ℝ) ≤ 0.696777783802 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667864602 : ℝ)) (Q := (0.626667864602 : ℝ))
      (s := (0.779286460473 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790616195054 : ℝ)) (R := (0.791174921184 : ℝ)) (Q2 := (0.626667864602 : ℝ)) (T := (0.835205230179 : ℝ))
    (B := ((6987558683422727/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (104408375327/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6981755743926729/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623861210236 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522041876635 : ℝ)) (s := (0.852919854992 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625856841474 : ℝ) ≤ 0.696195034487 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625856841474 : ℝ)) (Q := (0.625856841474 : ℝ))
      (s := (0.779937955212 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790104066591 : ℝ)) (R := (0.790662792721 : ℝ)) (Q2 := (0.625856841474 : ℝ)) (T := (0.834855895645 : ℝ))
    (B := ((6981755743926729/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52084466841/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3487979659124509/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623052232199 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520844668410 : ℝ)) (s := (0.853651469506 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625046372796 : ℝ) ≤ 0.695612967472 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625046372796 : ℝ)) (Q := (0.625046372796 : ℝ))
      (s := (0.780587619589 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789591956650 : ℝ)) (R := (0.790150682780 : ℝ)) (Q2 := (0.625046372796 : ℝ)) (T := (0.834506824144 : ℝ))
    (B := ((3487979659124509/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259823730093/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (278806775822803/400000000000000) := by
  have hk1 : kappa q ≤ 0.622243807309 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519647460186 : ℝ)) (s := (0.854380779935 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624236457912 : ℝ) ≤ 0.695031581460 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624236457912 : ℝ)) (Q := (0.624236457912 : ℝ))
      (s := (0.781235460418 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789079864853 : ℝ)) (R := (0.789638590983 : ℝ)) (Q2 := (0.624236457912 : ℝ)) (T := (0.834158015227 : ℝ))
    (B := ((278806775822803/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259225125981/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964385965113079/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621435934915 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518450251962 : ℝ)) (s := (0.855107792177 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623427096171 : ℝ) ≤ 0.694450875161 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623427096171 : ℝ)) (Q := (0.623427096171 : ℝ))
      (s := (0.781881484472 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788567790822 : ℝ)) (R := (0.789126516952 : ℝ)) (Q2 := (0.623427096171 : ℝ)) (T := (0.833809468449 : ℝ))
    (B := ((6964385965113079/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517253043737/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1739652254035911/2500000000000000) := by
  have hk1 : kappa q ≤ 0.620628614366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517253043737 : ℝ)) (s := (0.855832512087 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622618286922 : ℝ) ≤ 0.693870847288 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622618286922 : ℝ)) (Q := (0.622618286922 : ℝ))
      (s := (0.782525698486 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788055734180 : ℝ)) (R := (0.788614460310 : ℝ)) (Q2 := (0.622618286922 : ℝ)) (T := (0.833461183366 : ℝ))
    (B := ((1739652254035911/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516055835513/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (139056770759391/200000000000000) := by
  have hk1 : kappa q ≤ 0.619821845018 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516055835513 : ℝ)) (s := (0.856554945484 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621810029517 : ℝ) ≤ 0.693291496555 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621810029517 : ℝ)) (Q := (0.621810029517 : ℝ))
      (s := (0.783168109152 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787543694550 : ℝ)) (R := (0.788102420680 : ℝ)) (Q2 := (0.621810029517 : ℝ)) (T := (0.833113159534 : ℝ))
    (B := ((139056770759391/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64357328411/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1736768629985121/2500000000000000) := by
  have hk1 : kappa q ≤ 0.619015626230 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514858627288 : ℝ)) (s := (0.857275098150 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621002323315 : ℝ) ≤ 0.692712821685 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621002323315 : ℝ)) (Q := (0.621002323315 : ℝ))
      (s := (0.783808723119 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787031671559 : ℝ)) (R := (0.787590397689 : ℝ)) (Q2 := (0.621002323315 : ℝ)) (T := (0.832765396513 : ℝ))
    (B := ((1736768629985121/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64207677383/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6941316951447777/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618209957361 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513661419064 : ℝ)) (s := (0.857992975826 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620195167676 : ℝ) ≤ 0.692134821405 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620195167676 : ℝ)) (Q := (0.620195167676 : ℝ))
      (s := (0.784447546999 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786519664833 : ℝ)) (R := (0.787078390963 : ℝ)) (Q2 := (0.620195167676 : ℝ)) (T := (0.832417893863 : ℝ))
    (B := ((6941316951447777/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12811605271/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935565821924153/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617404837775 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512464210840 : ℝ)) (s := (0.858708584218 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619388561958 : ℝ) ≤ 0.691557494438 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619388561958 : ℝ)) (Q := (0.619388561958 : ℝ))
      (s := (0.785084587364 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786007673997 : ℝ)) (R := (0.786566400127 : ℝ)) (Q2 := (0.619388561958 : ℝ)) (T := (0.832070651144 : ℝ))
    (B := ((6935565821924153/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102253400523/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1732455280210867/2500000000000000) := by
  have hk1 : kappa q ≤ 0.616600266839 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511267002615 : ℝ)) (s := (0.859421928995 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618582505532 : ℝ) ≤ 0.690980839523 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618582505532 : ℝ)) (Q := (0.618582505532 : ℝ))
      (s := (0.785719850742 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785495698681 : ℝ)) (R := (0.786054424811 : ℝ)) (Q2 := (0.618582505532 : ℝ)) (T := (0.831723667921 : ℝ))
    (B := ((1732455280210867/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510069794391/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3462041418860229/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615796243924 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510069794391 : ℝ)) (s := (0.860133015789 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617776997764 : ℝ) ≤ 0.690404855395 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617776997764 : ℝ)) (Q := (0.617776997764 : ℝ))
      (s := (0.786353343628 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784983738514 : ℝ)) (R := (0.785542464644 : ℝ)) (Q2 := (0.617776997764 : ℝ)) (T := (0.831376943758 : ℝ))
    (B := ((3462041418860229/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508872586167/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918350962110493/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614992768404 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508872586167 : ℝ)) (s := (0.860841850196 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616972038030 : ℝ) ≤ 0.689829540797 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616972038030 : ℝ)) (Q := (0.616972038030 : ℝ))
      (s := (0.786985072470 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784471793127 : ℝ)) (R := (0.785030519257 : ℝ)) (Q2 := (0.616972038030 : ℝ)) (T := (0.831030478222 : ℝ))
    (B := ((6918350962110493/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253837688971/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912625483609321/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614189839653 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507675377942 : ℝ)) (s := (0.861548437775 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616167625701 : ℝ) ≤ 0.689254894474 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616167625701 : ℝ)) (Q := (0.616167625701 : ℝ))
      (s := (0.787615043685 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783959862149 : ℝ)) (R := (0.784518588279 : ℝ)) (Q2 := (0.616167625701 : ℝ)) (T := (0.830684270881 : ℝ))
    (B := ((6912625483609321/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253239084859/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906906391852829/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613387457052 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506478169718 : ℝ)) (s := (0.862252784049 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615363760156 : ℝ) ≤ 0.688680915175 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615363760156 : ℝ)) (Q := (0.615363760156 : ℝ))
      (s := (0.788243263649 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783447945213 : ℝ)) (R := (0.784006671343 : ℝ)) (Q2 := (0.615363760156 : ℝ)) (T := (0.830338321303 : ℝ))
    (B := ((6906906391852829/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505280961493/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450596838258397/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612585619984 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505280961493 : ℝ)) (s := (0.862954894507 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614560440779 : ℝ) ≤ 0.688107601656 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614560440779 : ℝ)) (Q := (0.614560440779 : ℝ))
      (s := (0.788869738696 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782936041954 : ℝ)) (R := (0.783494768084 : ℝ)) (Q2 := (0.614560440779 : ℝ)) (T := (0.829992629060 : ℝ))
    (B := ((3450596838258397/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504083753269/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895487327316643/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611784327836 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504083753269 : ℝ)) (s := (0.863654774601 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613757666957 : ℝ) ≤ 0.687534952678 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613757666957 : ℝ)) (Q := (0.613757666957 : ℝ))
      (s := (0.789494475125 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782424152007 : ℝ)) (R := (0.782982878137 : ℝ)) (Q2 := (0.613757666957 : ℝ)) (T := (0.829647193726 : ℝ))
    (B := ((6895487327316643/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100577309009/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1722446833501803/2500000000000000) := by
  have hk1 : kappa q ≤ 0.610983579995 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502886545045 : ℝ)) (s := (0.864352429749 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612955438071 : ℝ) ≤ 0.686962966999 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612955438071 : ℝ)) (Q := (0.612955438071 : ℝ))
      (s := (0.790117479202 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781912275004 : ℝ)) (R := (0.782471001134 : ℝ)) (Q2 := (0.612955438071 : ℝ)) (T := (0.829302014873 : ℝ))
    (B := ((1722446833501803/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25084466841/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1721023421595627/2500000000000000) := by
  have hk1 : kappa q ≤ 0.610183375854 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501689336820 : ℝ)) (s := (0.865047865336 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612153753517 : ℝ) ≤ 0.686391643390 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612153753517 : ℝ)) (Q := (0.612153753517 : ℝ))
      (s := (0.790738757148 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781400410584 : ℝ)) (R := (0.781959136714 : ℝ)) (Q2 := (0.612153753517 : ℝ)) (T := (0.828957092079 : ℝ))
    (B := ((1721023421595627/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125123032149/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (275136254971019/400000000000000) := by
  have hk1 : kappa q ≤ 0.609383714809 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500492128596 : ℝ)) (s := (0.865741086708 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611352612689 : ℝ) ≤ 0.685820980621 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611352612689 : ℝ)) (Q := (0.611352612689 : ℝ))
      (s := (0.791358315151 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780888558385 : ℝ)) (R := (0.781447284515 : ℝ)) (Q2 := (0.611352612689 : ℝ)) (T := (0.828612424921 : ℝ))
    (B := ((275136254971019/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (124823730093/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1718181346889439/2500000000000000) := by
  have hk1 : kappa q ≤ 0.608584596258 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499294920372 : ℝ)) (s := (0.866432099181 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610552014984 : ℝ) ≤ 0.685250977468 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610552014984 : ℝ)) (Q := (0.610552014984 : ℝ))
      (s := (0.791976159363 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780376718044 : ℝ)) (R := (0.780935444174 : ℝ)) (Q2 := (0.610552014984 : ℝ)) (T := (0.828268012978 : ℝ))
    (B := ((1718181346889439/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498097712147/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433525358069733/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607786019602 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498097712147 : ℝ)) (s := (0.867120908037 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609751959800 : ℝ) ≤ 0.684681632710 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609751959800 : ℝ)) (Q := (0.609751959800 : ℝ))
      (s := (0.792592295901 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779864889201 : ℝ)) (R := (0.780423615331 : ℝ)) (Q2 := (0.609751959800 : ℝ)) (T := (0.827923855830 : ℝ))
    (B := ((3433525358069733/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496900503923/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861382349968959/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606987984248 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496900503923 : ℝ)) (s := (0.867807518521 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608952446546 : ℝ) ≤ 0.684112945134 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608952446546 : ℝ)) (Q := (0.608952446546 : ℝ))
      (s := (0.793206730838 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779353071499 : ℝ)) (R := (0.779911797629 : ℝ)) (Q2 := (0.608952446546 : ℝ)) (T := (0.827579953062 : ℝ))
    (B := ((6861382349968959/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247851647849/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (34278601395163/50000000000000) := by
  have hk1 : kappa q ≤ 0.606190489602 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495703295698 : ℝ)) (s := (0.868491935849 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608153474626 : ℝ) ≤ 0.683544913527 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608153474626 : ℝ)) (Q := (0.608153474626 : ℝ))
      (s := (0.793819470220 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778841264578 : ℝ)) (R := (0.779399990708 : ℝ)) (Q2 := (0.608153474626 : ℝ)) (T := (0.827236304256 : ℝ))
    (B := ((34278601395163/50000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247253043737/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (342503224667727/500000000000000) := by
  have hk1 : kappa q ≤ 0.605393535078 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494506087474 : ℝ)) (s := (0.869174165201 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607355043451 : ℝ) ≤ 0.682977536682 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607355043451 : ℝ)) (Q := (0.607355043451 : ℝ))
      (s := (0.794430520055 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778329468082 : ℝ)) (R := (0.778888194212 : ℝ)) (Q2 := (0.607355043451 : ℝ)) (T := (0.826892909000 : ℝ))
    (B := ((342503224667727/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1973235517/4000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844414982996491/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604597120087 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493308879250 : ℝ)) (s := (0.869854211724 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606557152433 : ℝ) ≤ 0.682410813397 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606557152433 : ℝ)) (Q := (0.606557152433 : ℝ))
      (s := (0.795039886316 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777817681654 : ℝ)) (R := (0.778376407784 : ℝ)) (Q2 := (0.606557152433 : ℝ)) (T := (0.826549766880 : ℝ))
    (B := ((6844414982996491/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19684466841/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1367754347611501/2000000000000000) := by
  have hk1 : kappa q ≤ 0.603801244048 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492111671025 : ℝ)) (s := (0.870532080536 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605759800989 : ℝ) ≤ 0.681844742473 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605759800989 : ℝ)) (Q := (0.605759800989 : ℝ))
      (s := (0.795647574939 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777305904940 : ℝ)) (R := (0.777864631070 : ℝ)) (Q2 := (0.605759800989 : ℝ)) (T := (0.826206877486 : ℝ))
    (B := ((1367754347611501/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (490914462801/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6833134748673751/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603005906382 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490914462801 : ℝ)) (s := (0.871207776718 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604962988540 : ℝ) ≤ 0.681279322717 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604962988540 : ℝ)) (Q := (0.604962988540 : ℝ))
      (s := (0.796253591827 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776794137587 : ℝ)) (R := (0.777352863717 : ℝ)) (Q2 := (0.604962988540 : ℝ)) (T := (0.825864240410 : ℝ))
    (B := ((6833134748673751/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30607328411/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827504005018299/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602211106511 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489717254576 : ℝ)) (s := (0.871881305323 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604166714506 : ℝ) ≤ 0.680714552938 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604166714506 : ℝ)) (Q := (0.604166714506 : ℝ))
      (s := (0.796857942850 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776282379240 : ℝ)) (R := (0.776841105370 : ℝ)) (Q2 := (0.604166714506 : ℝ)) (T := (0.825521855243 : ℝ))
    (B := ((6827504005018299/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30532502897/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6821879497300903/10000000000000000) := by
  have hk1 : kappa q ≤ 0.601416843865 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488520046352 : ℝ)) (s := (0.872552671369 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603370978315 : ℝ) ≤ 0.680150431951 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603370978315 : ℝ)) (Q := (0.603370978315 : ℝ))
      (s := (0.797460633842 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775770629550 : ℝ)) (R := (0.776329355680 : ℝ)) (Q2 := (0.603370978315 : ℝ)) (T := (0.825179721581 : ℝ))
    (B := ((6821879497300903/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (30457677383/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852032651970973/1250000000000000) := by
  have hk1 : kappa q ≤ 0.600623117872 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487322838128 : ℝ)) (s := (0.873221879845 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602575779395 : ℝ) ≤ 0.679586958574 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602575779395 : ℝ)) (Q := (0.602575779395 : ℝ))
      (s := (0.798061670604 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775258888165 : ℝ)) (R := (0.775817614295 : ℝ)) (Q2 := (0.602575779395 : ℝ)) (T := (0.824837839019 : ℝ))
    (B := ((852032651970973/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486125629903/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405324575350709/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599829927965 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486125629903 : ℝ)) (s := (0.873888935708 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601781117179 : ℝ) ≤ 0.679024131633 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601781117179 : ℝ)) (Q := (0.601781117179 : ℝ))
      (s := (0.798661058903 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774747154736 : ℝ)) (R := (0.775305880866 : ℝ)) (Q2 := (0.601781117179 : ℝ)) (T := (0.824496207155 : ℝ))
    (B := ((3405324575350709/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (484928421679/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6805043292420327/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599037273582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484928421679 : ℝ)) (s := (0.874553843882 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600986991103 : ℝ) ≤ 0.678461949954 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600986991103 : ℝ)) (Q := (0.600986991103 : ℝ))
      (s := (0.799258804472 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774235428916 : ℝ)) (R := (0.774794155046 : ℝ)) (Q2 := (0.600986991103 : ℝ)) (T := (0.824154825591 : ℝ))
    (B := ((6805043292420327/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96746242691/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (424965226954929/625000000000000) := by
  have hk1 : kappa q ≤ 0.598245154161 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483731213455 : ℝ)) (s := (0.875216609263 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600193400605 : ℝ) ≤ 0.677900412369 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600193400605 : ℝ)) (Q := (0.600193400605 : ℝ))
      (s := (0.799854913013 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773723710357 : ℝ)) (R := (0.774282436487 : ℝ)) (Q2 := (0.600193400605 : ℝ)) (T := (0.823813693926 : ℝ))
    (B := ((424965226954929/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48253400523/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (679385015766701/1000000000000000) := by
  have hk1 : kappa q ≤ 0.597453569144 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482534005230 : ℝ)) (s := (0.875877236716 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599400345123 : ℝ) ≤ 0.677339517712 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599400345123 : ℝ)) (Q := (0.599400345123 : ℝ))
      (s := (0.800449390197 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773211998711 : ℝ)) (R := (0.773770724841 : ℝ)) (Q2 := (0.599400345123 : ℝ)) (T := (0.823472811762 : ℝ))
    (B := ((679385015766701/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (240668398503/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788262862010167/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596662517978 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481336797006 : ℝ)) (s := (0.876535731074 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598607824106 : ℝ) ≤ 0.676779264828 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598607824106 : ℝ)) (Q := (0.598607824106 : ℝ))
      (s := (0.801042241658 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772700293636 : ℝ)) (R := (0.773259019766 : ℝ)) (Q2 := (0.598607824106 : ℝ)) (T := (0.823132178707 : ℝ))
    (B := ((6788262862010167/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480139588781/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1695670252522007/2500000000000000) := by
  have hk1 : kappa q ≤ 0.595872000111 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480139588781 : ℝ)) (s := (0.877192097141 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597815836999 : ℝ) ≤ 0.676219652557 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597815836999 : ℝ)) (Q := (0.597815836999 : ℝ))
      (s := (0.801633473000 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772188594786 : ℝ)) (R := (0.772747320916 : ℝ)) (Q2 := (0.597815836999 : ℝ)) (T := (0.822791794366 : ℝ))
    (B := ((1695670252522007/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (478942380557/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777104820036589/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595082014996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478942380557 : ℝ)) (s := (0.877846339690 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597024383256 : ℝ) ≤ 0.675660679753 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597024383256 : ℝ)) (Q := (0.597024383256 : ℝ))
      (s := (0.802223089794 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771676901820 : ℝ)) (R := (0.772235627950 : ℝ)) (Q2 := (0.597024383256 : ℝ)) (T := (0.822451658348 : ℝ))
    (B := ((6777104820036589/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12400 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477745172333/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1692883695528487/2500000000000000) := by
  have hk1 : kappa q ≤ 0.594292562087 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477745172333 : ℝ)) (s := (0.878498463467 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596233462329 : ℝ) ≤ 0.675102345266 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596233462329 : ℝ)) (Q := (0.596233462329 : ℝ))
      (s := (0.802811097581 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771165214396 : ℝ)) (R := (0.771723940526 : ℝ)) (Q2 := (0.596233462329 : ℝ)) (T := (0.822111770262 : ℝ))
    (B := ((1692883695528487/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S2
namespace BstLean.Part269.S2
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12400 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.053122334932 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S2.wn_upper (by omega : 12400 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010724570072 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036243641051)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010724570072 + 2 * 0.737676 / 12400) := by gcongr
    _ ≤ (0.053122334932 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12400 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12400 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.355287256600 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12400 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.355287256600 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12400 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.004091684411 + 0.003376189719 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004091684411 + 0.003376189719 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.355287256600 ≤ R)
    (hB : (X + 0.053122334932 + R + 0.008583853148) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008583853148 := by
    convert (BstLean.Part269.S2.finite_centre_upper (by omega : 12400 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (86340655381/1000000000000)
  | 2 => (10912513691/125000000000)
  | 3 => (17652062029/200000000000)
  | 4 => (4461163123/50000000000)
  | 5 => (5636960637/62500000000)
  | 6 => (18233498369/200000000000)
  | 7 => (92155001771/1000000000000)
  | 8 => (46578927987/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.004091684411 + 0.003376189719 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011098417588 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.004091684411 + 0.003376189719 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011214767295 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.004091684411 + 0.003376189719 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011330732707 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.004091684411 + 0.003376189719 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011446322251 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.004091684411 + 0.003376189719 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011561544109 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.004091684411 + 0.003376189719 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011676406110 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.004091684411 + 0.003376189719 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011790915871 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12400 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.004091684411 + 0.003376189719 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011905080682 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12400 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g) :
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

end BstLean.Part269.S2

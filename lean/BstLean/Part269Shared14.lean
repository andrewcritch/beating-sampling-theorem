import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S14
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12700 ≤ n) : wn n ≤ 1.035809221007 := by
  have hnR : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.694276695846 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.694276695846 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035809221007 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12700 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12700 + 24 / (12700 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12700 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008481424533 : ℝ) := by
  have hnR : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.694276695846 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12700 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035809221007 * (81 / 1000 / 12700)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035809221007 * n *
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
        4 * (1 / 2.506628) * 1.035809221007 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035809221007 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035809221007 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12700)) / 112.694276695846 := by gcongr
    _ ≤ (0.008481424533 : ℝ) := by norm_num

end BstLean.Part269.S14
namespace BstLean.Part269.S14
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12700 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12700 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12700 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12700 + 0.008481424533 / 112.694276695846) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12700 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12700 := by gcongr
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
  have hn : (112.694276695846 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S14.finite_centre_upper (by omega : 12700 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528060522087/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (109534727735831/156250000000000) := by
  have hk1 : kappa q ≤ 0.627936535444 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528060522087 : ℝ)) (s := (0.849206738677 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629909165668 : ℝ) ≤ 0.699109617724 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629909165668 : ℝ)) (Q := (0.629909165668 : ℝ))
      (s := (0.776668811662 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792672843128 : ℝ)) (R := (0.793218371003 : ℝ)) (Q2 := (0.629909165668 : ℝ)) (T := (0.836601610223 : ℝ))
    (B := ((109534727735831/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105373314859/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1751102455209183/2500000000000000) := by
  have hk1 : kappa q ≤ 0.627126976610 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526866574295 : ℝ)) (s := (0.849948005993 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629098130480 : ℝ) ≤ 0.698525721497 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629098130480 : ℝ)) (Q := (0.629098130480 : ℝ))
      (s := (0.777325891906 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792162027238 : ℝ)) (R := (0.792707555113 : ℝ)) (Q2 := (0.629098130480 : ℝ)) (T := (0.836252172488 : ℝ))
    (B := ((1751102455209183/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65709078313/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (218706362123651/312500000000000) := by
  have hk1 : kappa q ≤ 0.626317971221 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525672626504 : ℝ)) (s := (0.850686951672 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628287649388 : ℝ) ≤ 0.697942509066 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628287649388 : ℝ)) (Q := (0.628287649388 : ℝ))
      (s := (0.777981124210 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791651231294 : ℝ)) (R := (0.792196759169 : ℝ)) (Q2 := (0.628287649388 : ℝ)) (T := (0.835902998155 : ℝ))
    (B := ((218706362123651/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524478678713/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (69928038655507/100000000000000) := by
  have hk1 : kappa q ≤ 0.625509518616 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524478678713 : ℝ)) (s := (0.851423581760 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477721729 : ℝ) ≤ 0.697359979131 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477721729 : ℝ)) (Q := (0.627477721729 : ℝ))
      (s := (0.778634515504 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791140454916 : ℝ)) (R := (0.791685982791 : ℝ)) (Q2 := (0.627477721729 : ℝ)) (T := (0.835554086777 : ℝ))
    (B := ((69928038655507/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523284730921/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3493505321379431/5000000000000000) := by
  have hk1 : kappa q ≤ 0.624701618135 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523284730921 : ℝ)) (s := (0.852157902261 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668346839 : ℝ) ≤ 0.696778130392 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668346839 : ℝ)) (Q := (0.626668346839 : ℝ))
      (s := (0.779286072679 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790629697724 : ℝ)) (R := (0.791175225599 : ℝ)) (Q2 := (0.626668346839 : ℝ)) (T := (0.835205437902 : ℝ))
    (B := ((3493505321379431/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52209078313/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1396244781752977/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623894269123 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522090783130 : ℝ)) (s := (0.852889919141 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859524066 : ℝ) ≤ 0.696196961558 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859524066 : ℝ)) (Q := (0.625859524066 : ℝ))
      (s := (0.779935802574 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790118959342 : ℝ)) (R := (0.790664487217 : ℝ)) (Q2 := (0.625859524066 : ℝ)) (T := (0.834857051087 : ℝ))
    (B := ((1396244781752977/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520896835339/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1395088730559021/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623087470927 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520896835339 : ℝ)) (s := (0.853619638325 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625051252754 : ℝ) ≤ 0.695616471339 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625051252754 : ℝ)) (Q := (0.625051252754 : ℝ))
      (s := (0.780583711995 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789608239392 : ℝ)) (R := (0.790153767267 : ℝ)) (Q2 := (0.625051252754 : ℝ)) (T := (0.834508925886 : ℝ))
    (B := ((1395088730559021/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519702887547/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (174241746602959/250000000000000) := by
  have hk1 : kappa q ≤ 0.622281222897 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519702887547 : ℝ)) (s := (0.854347065703 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624243532251 : ℝ) ≤ 0.695036658449 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624243532251 : ℝ)) (Q := (0.624243532251 : ℝ))
      (s := (0.781229807703 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789097537498 : ℝ)) (R := (0.789643065373 : ℝ)) (Q2 := (0.624243532251 : ℝ)) (T := (0.834161061853 : ℝ))
    (B := ((174241746602959/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129627234939/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1740975633011431/2500000000000000) := by
  have hk1 : kappa q ≤ 0.621475524388 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518508939756 : ℝ)) (s := (0.855072207123 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623436361911 : ℝ) ≤ 0.694457521609 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623436361911 : ℝ)) (Q := (0.623436361911 : ℝ))
      (s := (0.781874096417 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788586853286 : ℝ)) (R := (0.789132381161 : ℝ)) (Q2 := (0.623436361911 : ℝ)) (T := (0.833813458550 : ℝ))
    (B := ((1740975633011431/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129328747991/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1391628329186049/2000000000000000) := by
  have hk1 : kappa q ≤ 0.620670374754 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517314991964 : ℝ)) (s := (0.855795068396 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622629741089 : ℝ) ≤ 0.693879059539 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622629741089 : ℝ)) (Q := (0.622629741089 : ℝ))
      (s := (0.782516584816 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788076186382 : ℝ)) (R := (0.788621714257 : ℝ)) (Q2 := (0.622629741089 : ℝ)) (T := (0.833466115532 : ℝ))
    (B := ((1391628329186049/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516121044173/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1390477439033337/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619865773357 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516121044173 : ℝ)) (s := (0.856515655293 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621823669144 : ℝ) ≤ 0.693301270969 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621823669144 : ℝ)) (Q := (0.621823669144 : ℝ))
      (s := (0.783157279538 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787565536413 : ℝ)) (R := (0.788111064288 : ℝ)) (Q2 := (0.621823669144 : ℝ)) (T := (0.833119032363 : ℝ))
    (B := ((1390477439033337/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257463548191/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6946639169191257/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619061719559 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514927096382 : ℝ)) (s := (0.857233973552 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621018145438 : ℝ) ≤ 0.692724154630 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621018145438 : ℝ)) (Q := (0.621018145438 : ℝ))
      (s := (0.783796187180 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787054903007 : ℝ)) (R := (0.787600430882 : ℝ)) (Q2 := (0.621018145438 : ℝ)) (T := (0.832772208604 : ℝ))
    (B := ((6946639169191257/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51373314859/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940897557481377/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618258212725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513733148590 : ℝ)) (s := (0.857950028872 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620213169333 : ℝ) ≤ 0.692147709253 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620213169333 : ℝ)) (Q := (0.620213169333 : ℝ))
      (s := (0.784433314302 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786544285793 : ℝ)) (R := (0.787089813668 : ℝ)) (Q2 := (0.620213169333 : ℝ)) (T := (0.832425643817 : ℝ))
    (B := ((6940897557481377/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (512539200799/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935162349555401/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617455252225 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512539200799 : ℝ)) (s := (0.858663826911 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619408740199 : ℝ) ≤ 0.691571933582 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619408740199 : ℝ)) (Q := (0.619408740199 : ℝ))
      (s := (0.785068667421 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786033684401 : ℝ)) (R := (0.786579212276 : ℝ)) (Q2 := (0.619408740199 : ℝ)) (T := (0.832079337569 : ℝ))
    (B := ((6935162349555401/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31959078313/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (346471676748619/500000000000000) := by
  have hk1 : kappa q ≤ 0.616652837430 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511345253008 : ℝ)) (s := (0.859375373296 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618604857408 : ℝ) ≤ 0.690996826358 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618604857408 : ℝ)) (Q := (0.618604857408 : ℝ))
      (s := (0.785702253014 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785523098463 : ℝ)) (R := (0.786068626338 : ℝ)) (Q2 := (0.618604857408 : ℝ)) (T := (0.831733289427 : ℝ))
    (B := ((346471676748619/500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249097317/488281250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6923711103331809/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615850967715 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510151305216 : ℝ)) (s := (0.860084673615 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617801520329 : ℝ) ≤ 0.690422386328 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617801520329 : ℝ)) (Q := (0.617801520329 : ℝ))
      (s := (0.786334077527 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785012527609 : ℝ)) (R := (0.785558055484 : ℝ)) (Q2 := (0.617801520329 : ℝ)) (T := (0.831387498957 : ℝ))
    (B := ((6923711103331809/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (20358294297/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3458997522136689/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615049642460 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508957357425 : ℝ)) (s := (0.860791733420 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616998728345 : ℝ) ≤ 0.689848612246 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616998728345 : ℝ)) (Q := (0.616998728345 : ℝ))
      (s := (0.786964147355 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784501971475 : ℝ)) (R := (0.785047499350 : ℝ)) (Q2 := (0.616998728345 : ℝ)) (T := (0.831041965731 : ℝ))
    (B := ((3458997522136689/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507763409633/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912285347476727/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614248861044 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507763409633 : ℝ)) (s := (0.861496558228 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616196480833 : ℝ) ≤ 0.689275502867 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616196480833 : ℝ)) (Q := (0.616196480833 : ℝ))
      (s := (0.787592468863 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783991429693 : ℝ)) (R := (0.784536957568 : ℝ)) (Q2 := (0.616196480833 : ℝ)) (T := (0.830696689320 : ℝ))
    (B := ((6912285347476727/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253284730921/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1726645500665301/2500000000000000) := by
  have hk1 : kappa q ≤ 0.613448622853 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506569461842 : ℝ)) (s := (0.862199153520 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615394777176 : ℝ) ≤ 0.688703056949 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615394777176 : ℝ)) (Q := (0.615394777176 : ℝ))
      (s := (0.788219048378 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783480901899 : ℝ)) (R := (0.784026429774 : ℝ)) (Q2 := (0.615394777176 : ℝ)) (T := (0.830351669295 : ℝ))
    (B := ((1726645500665301/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505375514051/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450442499792813/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612648927275 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505375514051 : ℝ)) (s := (0.862899524741 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614593616765 : ℝ) ≤ 0.688131273261 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614593616765 : ℝ)) (Q := (0.614593616765 : ℝ))
      (s := (0.788843892182 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782970387731 : ℝ)) (R := (0.783515915606 : ℝ)) (Q2 := (0.614593616765 : ℝ)) (T := (0.830006905234 : ℝ))
    (B := ((3450442499792813/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504181566259/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1379038865609607/2000000000000000) := by
  have hk1 : kappa q ≤ 0.611849773699 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504181566259 : ℝ)) (s := (0.863597677304 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613792998984 : ℝ) ≤ 0.687560150568 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613792998984 : ℝ)) (Q := (0.613792998984 : ℝ))
      (s := (0.789467006530 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782459886823 : ℝ)) (R := (0.783005414698 : ℝ)) (Q2 := (0.613792998984 : ℝ)) (T := (0.829662396711 : ℝ))
    (B := ((1379038865609607/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125746904617/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (861188747235683/1250000000000000) := by
  have hk1 : kappa q ≤ 0.611051161520 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502987618468 : ℝ)) (s := (0.864293616585 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612992923229 : ℝ) ≤ 0.686989687643 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612992923229 : ℝ)) (Q := (0.612992923229 : ℝ))
      (s := (0.790088397632 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781949398816 : ℝ)) (R := (0.782494926691 : ℝ)) (Q2 := (0.612992923229 : ℝ)) (T := (0.829318143303 : ℝ))
    (B := ((861188747235683/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501793670677/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1376766387794741/2000000000000000) := by
  have hk1 : kappa q ≤ 0.610253090135 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501793670677 : ℝ)) (s := (0.864987347924 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612193388894 : ℝ) ≤ 0.686419883263 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612193388894 : ℝ)) (Q := (0.612193388894 : ℝ))
      (s := (0.790708071664 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781438923348 : ℝ)) (R := (0.781984451223 : ℝ)) (Q2 := (0.612193388894 : ℝ)) (T := (0.828974144590 : ℝ))
    (B := ((1376766387794741/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100119944577/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (687816020122707/1000000000000000) := by
  have hk1 : kappa q ≤ 0.609455558943 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500599722885 : ℝ)) (s := (0.865678876633 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611394395379 : ℝ) ≤ 0.685850736210 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611394395379 : ℝ)) (Q := (0.611394395379 : ℝ))
      (s := (0.791326034767 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780928460060 : ℝ)) (R := (0.781473987935 : ℝ)) (Q2 := (0.611394395379 : ℝ)) (T := (0.828630400153 : ℝ))
    (B := ((687816020122707/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249702887547/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1718123688649541/2500000000000000) := by
  have hk1 : kappa q ≤ 0.608658567349 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499405775094 : ℝ)) (s := (0.866368207983 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610595942086 : ℝ) ≤ 0.685282245269 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610595942086 : ℝ)) (Q := (0.610595942086 : ℝ))
      (s := (0.791942293042 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780418008594 : ℝ)) (R := (0.780963536469 : ℝ)) (Q2 := (0.610595942086 : ℝ)) (T := (0.828286909575 : ℝ))
    (B := ((1718123688649541/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249105913651/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433417794538829/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607862114758 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498211827302 : ℝ)) (s := (0.867055347217 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609798028420 : ℝ) ≤ 0.684714409230 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609798028420 : ℝ)) (Q := (0.609798028420 : ℝ))
      (s := (0.792556852558 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779907568591 : ℝ)) (R := (0.780453096466 : ℝ)) (Q2 := (0.609798028420 : ℝ)) (T := (0.827943672440 : ℝ))
    (B := ((3433417794538829/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497017879511/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6861182694694057/10000000000000000) := by
  have hk1 : kappa q ≤ 0.607066200580 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497017879511 : ℝ)) (s := (0.867740299541 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609000653791 : ℝ) ≤ 0.684147226888 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609000653791 : ℝ)) (Q := (0.609000653791 : ℝ))
      (s := (0.793169719343 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779397139697 : ℝ)) (R := (0.779942667572 : ℝ)) (Q2 := (0.609000653791 : ℝ)) (T := (0.827600688334 : ℝ))
    (B := ((6861182694694057/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12395598293/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855536061513479/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606270824227 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495823931720 : ℝ)) (s := (0.868423070130 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608203817608 : ℝ) ≤ 0.683580697038 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608203817608 : ℝ)) (Q := (0.608203817608 : ℝ))
      (s := (0.793780899397 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778886721555 : ℝ)) (R := (0.779432249430 : ℝ)) (Q2 := (0.608203817608 : ℝ)) (T := (0.827257956844 : ℝ))
    (B := ((6855536061513479/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61828747991/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1712473919909857/2500000000000000) := by
  have hk1 : kappa q ≤ 0.605475985115 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494629983928 : ℝ)) (s := (0.869103664128 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607407519288 : ℝ) ≤ 0.683014818486 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607407519288 : ℝ)) (Q := (0.607407519288 : ℝ))
      (s := (0.794390398679 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778376313812 : ℝ)) (R := (0.778921841687 : ℝ)) (Q2 := (0.607407519288 : ℝ)) (T := (0.826915477560 : ℝ))
    (B := ((1712473919909857/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493436036137/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422130769606289/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604681682664 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493436036137 : ℝ)) (s := (0.869782086641 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606611758247 : ℝ) ≤ 0.682449590037 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606611758247 : ℝ)) (Q := (0.606611758247 : ℝ))
      (s := (0.794998223116 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777865916114 : ℝ)) (R := (0.778411443989 : ℝ)) (Q2 := (0.606611758247 : ℝ)) (T := (0.826573250072 : ℝ))
    (B := ((3422130769606289/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246121044173/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838633630410549/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603887916294 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492242088346 : ℝ)) (s := (0.870458342749 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605816533907 : ℝ) ≤ 0.681885010502 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605816533907 : ℝ)) (Q := (0.605816533907 : ℝ))
      (s := (0.795604378599 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777355528109 : ℝ)) (R := (0.777901055984 : ℝ)) (Q2 := (0.605816533907 : ℝ)) (T := (0.826231273972 : ℝ))
    (B := ((6838633630410549/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (245524070277/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1708252985861923/2500000000000000) := by
  have hk1 : kappa q ≤ 0.603094685430 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491048140554 : ℝ)) (s := (0.871132437497 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605021845691 : ℝ) ≤ 0.681321078697 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605021845691 : ℝ)) (Q := (0.605021845691 : ℝ))
      (s := (0.796208870986 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776845149446 : ℝ)) (R := (0.777390677321 : ℝ)) (Q2 := (0.605021845691 : ℝ)) (T := (0.825889548857 : ℝ))
    (B := ((1708252985861923/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489854192763/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (853424558571859/1250000000000000) := by
  have hk1 : kappa q ≤ 0.602301989502 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489854192763 : ℝ)) (s := (0.871804375897 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604227693027 : ℝ) ≤ 0.680757793440 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604227693027 : ℝ)) (Q := (0.604227693027 : ℝ))
      (s := (0.796811706101 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776334779776 : ℝ)) (R := (0.776880307651 : ℝ)) (Q2 := (0.604227693027 : ℝ)) (T := (0.825548074319 : ℝ))
    (B := ((853424558571859/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488660244971/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1364357439215851/2000000000000000) := by
  have hk1 : kappa q ≤ 0.601509827940 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488660244971 : ℝ)) (s := (0.872474162933 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603434075345 : ℝ) ≤ 0.680195153558 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603434075345 : ℝ)) (Q := (0.603434075345 : ℝ))
      (s := (0.797412889734 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775824418750 : ℝ)) (R := (0.776369946625 : ℝ)) (Q2 := (0.603434075345 : ℝ)) (T := (0.825206849959 : ℝ))
    (B := ((1364357439215851/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24373314859/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816184116284093/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600718200179 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487466297180 : ℝ)) (s := (0.873141803555 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602640992078 : ℝ) ≤ 0.679633157875 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602640992078 : ℝ)) (Q := (0.602640992078 : ℝ))
      (s := (0.798012427640 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775314066019 : ℝ)) (R := (0.775859593894 : ℝ)) (Q2 := (0.602640992078 : ℝ)) (T := (0.824865875375 : ℝ))
    (B := ((6816184116284093/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486272349389/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3405293609774259/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599927105656 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486272349389 : ℝ)) (s := (0.873807302682 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601848442663 : ℝ) ≤ 0.679071805227 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601848442663 : ℝ)) (Q := (0.601848442663 : ℝ))
      (s := (0.798610325544 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774803721238 : ℝ)) (R := (0.775349249113 : ℝ)) (Q2 := (0.601848442663 : ℝ)) (T := (0.824525150168 : ℝ))
    (B := ((3405293609774259/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (485078401597/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804996496267331/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599136543811 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485078401597 : ℝ)) (s := (0.874470665206 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601056426539 : ℝ) ≤ 0.678511094449 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601056426539 : ℝ)) (Q := (0.601056426539 : ℝ))
      (s := (0.799206589135 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774293384060 : ℝ)) (R := (0.774838911935 : ℝ)) (Q2 := (0.601056426539 : ℝ)) (T := (0.824184673941 : ℝ))
    (B := ((6804996496267331/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241942226903/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1359882387374159/2000000000000000) := by
  have hk1 : kappa q ≤ 0.598346514088 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483884453806 : ℝ)) (s := (0.875131895982 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600264943148 : ℝ) ≤ 0.677951024381 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600264943148 : ℝ)) (Q := (0.600264943148 : ℝ))
      (s := (0.799801224073 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773783054141 : ℝ)) (R := (0.774328582016 : ℝ)) (Q2 := (0.600264943148 : ℝ)) (T := (0.823844446297 : ℝ))
    (B := ((1359882387374159/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96538101203/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793833531824429/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597557015935 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482690506015 : ℝ)) (s := (0.875790999842 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599473991938 : ℝ) ≤ 0.677391593870 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599473991938 : ℝ)) (Q := (0.599473991938 : ℝ))
      (s := (0.800394235980 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773272731139 : ℝ)) (R := (0.773818259014 : ℝ)) (Q2 := (0.599473991938 : ℝ)) (T := (0.823504466844 : ℝ))
    (B := ((6793833531824429/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481496558223/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (848532636584633/1250000000000000) := by
  have hk1 : kappa q ≤ 0.596768048800 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481496558223 : ℝ)) (s := (0.876447981583 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598683572356 : ℝ) ≤ 0.676832801766 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598683572356 : ℝ)) (Q := (0.598683572356 : ℝ))
      (s := (0.800985630453 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772762414710 : ℝ)) (R := (0.773307942585 : ℝ)) (Q2 := (0.598683572356 : ℝ)) (T := (0.823164735190 : ℝ))
    (B := ((848532636584633/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (234522759/488281250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (847836723485919/1250000000000000) := by
  have hk1 : kappa q ≤ 0.595979612136 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480302610432 : ℝ)) (s := (0.877102845973 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597893683853 : ℝ) ≤ 0.676274646920 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597893683853 : ℝ)) (Q := (0.597893683853 : ℝ))
      (s := (0.801575413052 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772252104513 : ℝ)) (R := (0.772797632388 : ℝ)) (Q2 := (0.597893683853 : ℝ)) (T := (0.822825250943 : ℝ))
    (B := ((847836723485919/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5988858283/12500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777132611642957/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595191705400 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479108662640 : ℝ)) (s := (0.877755597752 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597104325885 : ℝ) ≤ 0.675717128191 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597104325885 : ℝ)) (Q := (0.597104325885 : ℝ))
      (s := (0.802163589307 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771741800208 : ℝ)) (R := (0.772287328083 : ℝ)) (Q2 := (0.597104325885 : ℝ)) (T := (0.822486013715 : ℝ))
    (B := ((6777132611642957/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12700 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477914714849/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (826608588201/1220703125000) := by
  have hk1 : kappa q ≤ 0.594404328050 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477914714849 : ℝ)) (s := (0.878406241628 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596315497910 : ℝ) ≤ 0.675160244442 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596315497910 : ℝ)) (Q := (0.596315497910 : ℝ))
      (s := (0.802750164717 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771231501456 : ℝ)) (R := (0.771777029331 : ℝ)) (Q2 := (0.596315497910 : ℝ)) (T := (0.822147023120 : ℝ))
    (B := ((826608588201/1220703125000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S14
namespace BstLean.Part269.S14
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12700 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052484312798 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S14.wn_upper (by omega : 12700 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010597144914 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035809221007)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010597144914 + 2 * 0.737676 / 12700) := by gcongr
    _ ≤ (0.052484312798 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12700 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12700 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.694276695846 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12700 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.694276695846 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12700 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003533030491 + 0.003293667169 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003533030491 + 0.003293667169 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.694276695846 ≤ R)
    (hB : (X + 0.052484312798 + R + 0.008481424533) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008481424533 := by
    convert (BstLean.Part269.S14.finite_centre_upper (by omega : 12700 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (85420574807/1000000000000)
  | 2 => (86362050867/1000000000000)
  | 3 => (87301481949/1000000000000)
  | 4 => (17648048701/200000000000)
  | 5 => (11147500077/125000000000)
  | 6 => (18024550237/200000000000)
  | 7 => (2276771831/25000000000)
  | 8 => (23006794093/250000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003533030491 + 0.003293667169 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219117799916 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010966550519 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003533030491 + 0.003293667169 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220688257813 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011081517804 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003533030491 + 0.003293667169 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222238216857 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011196105361 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003533030491 + 0.003293667169 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223767885672 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011310321514 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003533030491 + 0.003293667169 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225277467646 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011424174351 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003533030491 + 0.003293667169 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226767159442 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011537671607 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003533030491 + 0.003293667169 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228237152878 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011650820808 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12700 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003533030491 + 0.003293667169 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229687633464 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011763629157 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12700 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g) :
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

end BstLean.Part269.S14

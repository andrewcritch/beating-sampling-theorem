import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S20
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12850 ≤ n) : wn n ≤ 1.035597771358 := by
  have hnR : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (113.357840487546 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (113.357840487546 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035597771358 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12850 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12850 + 24 / (12850 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12850 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008431564502 : ℝ) := by
  have hnR : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (113.357840487546 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12850 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035597771358 * (81 / 1000 / 12850)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035597771358 * n *
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
        4 * (1 / 2.506628) * 1.035597771358 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035597771358 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035597771358 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12850)) / 113.357840487546 := by gcongr
    _ ≤ (0.008431564502 : ℝ) := by norm_num

end BstLean.Part269.S20
namespace BstLean.Part269.S20
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12850 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12850 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12850 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12850 + 0.008431564502 / 113.357840487546) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12850 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12850 := by gcongr
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
  have hn : (113.357840487546 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S20.finite_centre_upper (by omega : 12850 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (13201909663/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1752481836479681/2500000000000000) := by
  have hk1 : kappa q ≤ 0.627947296085 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528076386520 : ℝ)) (s := (0.849196873523 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629905227874 : ℝ) ≤ 0.699106782062 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629905227874 : ℝ)) (Q := (0.629905227874 : ℝ))
      (s := (0.776672005352 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792676731804 : ℝ)) (R := (0.793215891649 : ℝ)) (Q2 := (0.629905227874 : ℝ)) (T := (0.836599913549 : ℝ))
    (B := ((1752481836479681/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131721006293/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004122543313091/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627138805227 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526884025172 : ℝ)) (s := (0.849937188279 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629095269118 : ℝ) ≤ 0.698523661995 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629095269118 : ℝ)) (Q := (0.629095269118 : ℝ))
      (s := (0.777328207628 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792166592508 : ℝ)) (R := (0.792705752353 : ℝ)) (Q2 := (0.629095269118 : ℝ)) (T := (0.836250939703 : ℝ))
    (B := ((7004122543313091/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (32855728989/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998324244533663/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626330866353 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525691663824 : ℝ)) (s := (0.850675187476 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628285862994 : ℝ) ≤ 0.697941223913 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628285862994 : ℝ)) (Q := (0.628285862994 : ℝ))
      (s := (0.777982566876 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791656473107 : ℝ)) (R := (0.792195632952 : ℝ)) (Q2 := (0.628285862994 : ℝ)) (T := (0.835902228562 : ℝ))
    (B := ((6998324244533663/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131124825619/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (55940259509771/80000000000000) := by
  have hk1 : kappa q ≤ 0.625523478806 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524499302476 : ℝ)) (s := (0.851410877135 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477008844 : ℝ) ≤ 0.697359466523 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477008844 : ℝ)) (Q := (0.627477008844 : ℝ))
      (s := (0.778635089996 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791146373224 : ℝ)) (R := (0.791685533069 : ℝ)) (Q2 := (0.627477008844 : ℝ)) (T := (0.835553779681 : ℝ))
    (B := ((55940259509771/80000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65413367641/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1746686778765061/2500000000000000) := by
  have hk1 : kappa q ≤ 0.624716641927 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523306941128 : ℝ)) (s := (0.852144263237 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668706006 : ℝ) ≤ 0.696778388529 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668706006 : ℝ)) (Q := (0.626668706006 : ℝ))
      (s := (0.779285783852 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790636292480 : ℝ)) (R := (0.791175452325 : ℝ)) (Q2 := (0.626668706006 : ℝ)) (T := (0.835205592612 : ℝ))
    (B := ((1746686778765061/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (26105728989/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3490484131388549/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623910355066 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522114579780 : ℝ)) (s := (0.852875351726 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625860953831 : ℝ) ≤ 0.696197988647 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625860953831 : ℝ)) (Q := (0.625860953831 : ℝ))
      (s := (0.779934655257 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790126230501 : ℝ)) (R := (0.790665390346 : ℝ)) (Q2 := (0.625860953831 : ℝ)) (T := (0.834857666913 : ℝ))
    (B := ((3490484131388549/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (8139409663/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1743798967785327/2500000000000000) := by
  have hk1 : kappa q ≤ 0.623104617570 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520922218432 : ℝ)) (s := (0.853604148505 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625053751663 : ℝ) ≤ 0.695618265589 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625053751663 : ℝ)) (Q := (0.625053751663 : ℝ))
      (s := (0.780581710990 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789616186909 : ℝ)) (R := (0.790155346754 : ℝ)) (Q2 := (0.625053751663 : ℝ)) (T := (0.834510002137 : ℝ))
    (B := ((1743798967785327/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519729857083/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (174235748236613/250000000000000) := by
  have hk1 : kappa q ≤ 0.622299428793 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519729857083 : ℝ)) (s := (0.854330659439 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624247098857 : ℝ) ≤ 0.695039218078 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624247098857 : ℝ)) (Q := (0.624247098857 : ℝ))
      (s := (0.781226957785 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789106161332 : ℝ)) (R := (0.789645321177 : ℝ)) (Q2 := (0.624247098857 : ℝ)) (T := (0.834162597845 : ℝ))
    (B := ((174235748236613/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103707499147/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392734085420079/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621494788092 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518537495735 : ℝ)) (s := (0.855054890354 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623440994768 : ℝ) ≤ 0.694460844837 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623440994768 : ℝ)) (Q := (0.623440994768 : ℝ))
      (s := (0.781870402332 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788596153396 : ℝ)) (R := (0.789135313241 : ℝ)) (Q2 := (0.623440994768 : ℝ)) (T := (0.833815453595 : ℝ))
    (B := ((1392734085420079/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517345134387/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6957917353444343/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620690694825 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517345134387 : ℝ)) (s := (0.855776847038 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622635438753 : ℝ) ≤ 0.693883144594 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622635438753 : ℝ)) (Q := (0.622635438753 : ℝ))
      (s := (0.782512051287 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788086162729 : ℝ)) (R := (0.788625322574 : ℝ)) (Q2 := (0.622635438753 : ℝ)) (T := (0.833468568949 : ℝ))
    (B := ((6957917353444343/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (516152773039/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (695217069793327/1000000000000000) := by
  have hk1 : kappa q ≤ 0.619887148354 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516152773039 : ℝ)) (s := (0.856496535244 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621830430171 : ℝ) ≤ 0.693306116079 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621830430171 : ℝ)) (Q := (0.621830430171 : ℝ))
      (s := (0.783151911263 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787576188958 : ℝ)) (R := (0.788115348803 : ℝ)) (Q2 := (0.621830430171 : ℝ)) (T := (0.833121943468 : ℝ))
    (B := ((695217069793327/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (514960411691/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473215225022657/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619084148044 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514960411691 : ℝ)) (s := (0.857213960684 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621025968388 : ℝ) ≤ 0.692729758030 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621025968388 : ℝ)) (Q := (0.621025968388 : ℝ))
      (s := (0.783789988829 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787066231713 : ℝ)) (R := (0.787605391558 : ℝ)) (Q2 := (0.621025968388 : ℝ)) (T := (0.832775576717 : ℝ))
    (B := ((3473215225022657/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513768050343/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (17351741498249/25000000000000) := by
  have hk1 : kappa q ≤ 0.618281693264 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513768050343 : ℝ)) (s := (0.857929129035 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620222052772 : ℝ) ≤ 0.692154069187 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620222052772 : ℝ)) (Q := (0.620222052772 : ℝ))
      (s := (0.784426290518 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786556290626 : ℝ)) (R := (0.787095450471 : ℝ)) (Q2 := (0.620222052772 : ℝ)) (T := (0.832429468260 : ℝ))
    (B := ((17351741498249/25000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102515137799/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6934969135255977/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617479783385 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512575688995 : ℝ)) (s := (0.858642045938 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619418682691 : ℝ) ≤ 0.691579048293 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619418682691 : ℝ)) (Q := (0.619418682691 : ℝ))
      (s := (0.785060822825 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786046365327 : ℝ)) (R := (0.786585525172 : ℝ)) (Q2 := (0.619418682691 : ℝ)) (T := (0.832083617665 : ℝ))
    (B := ((6934969135255977/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511383327647/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6929248047514777/10000000000000000) := by
  have hk1 : kappa q ≤ 0.616678417781 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511383327647 : ℝ)) (s := (0.859352716994 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618615857519 : ℝ) ≤ 0.691004694097 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618615857519 : ℝ)) (Q := (0.618615857519 : ℝ))
      (s := (0.785693592202 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785536455449 : ℝ)) (R := (0.786075615294 : ℝ)) (Q2 := (0.618615857519 : ℝ)) (T := (0.831738024500 : ℝ))
    (B := ((6929248047514777/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510190966299/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3461766662858281/5000000000000000) := by
  have hk1 : kappa q ≤ 0.615877595830 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510190966299 : ℝ)) (s := (0.860061147773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617813576636 : ℝ) ≤ 0.690431005354 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617813576636 : ℝ)) (Q := (0.617813576636 : ℝ))
      (s := (0.786324605061 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785026560627 : ℝ)) (R := (0.785565720472 : ℝ)) (Q2 := (0.617813576636 : ℝ)) (T := (0.831392688337 : ℝ))
    (B := ((3461766662858281/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (508998604951/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (172945623988547/250000000000000) := by
  have hk1 : kappa q ≤ 0.615077316912 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508998604951 : ℝ)) (s := (0.860767343804 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617011839415 : ℝ) ≤ 0.689857980816 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617011839415 : ℝ)) (Q := (0.617011839415 : ℝ))
      (s := (0.786953867785 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784516680493 : ℝ)) (R := (0.785055840338 : ℝ)) (Q2 := (0.617011839415 : ℝ)) (T := (0.831047608744 : ℝ))
    (B := ((172945623988547/250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507806243603/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912122938711021/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614277580412 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507806243603 : ℝ)) (s := (0.861471310584 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616210645243 : ℝ) ≤ 0.689285619247 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616210645243 : ℝ)) (Q := (0.616210645243 : ℝ))
      (s := (0.787581386709 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784006814684 : ℝ)) (R := (0.784545974529 : ℝ)) (Q2 := (0.616210645243 : ℝ)) (T := (0.830702785295 : ℝ))
    (B := ((6912122938711021/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (101322776451/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (215825851655743/312500000000000) := by
  have hk1 : kappa q ≤ 0.613478385715 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506613882255 : ℝ)) (s := (0.862173053573 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615409993505 : ℝ) ≤ 0.688713919411 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615409993505 : ℝ)) (Q := (0.615409993505 : ℝ))
      (s := (0.788207168132 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783496962837 : ℝ)) (R := (0.784036122682 : ℝ)) (Q2 := (0.615409993505 : ℝ)) (T := (0.830358217566 : ℝ))
    (B := ((215825851655743/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505421520907/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900737892159197/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612679732212 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505421520907 : ℝ)) (s := (0.862872578197 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614609883587 : ℝ) ≤ 0.688142880075 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614609883587 : ℝ)) (Q := (0.614609883587 : ℝ))
      (s := (0.788831218321 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782987124588 : ℝ)) (R := (0.783526284433 : ℝ)) (Q2 := (0.614609883587 : ℝ)) (T := (0.830013905131 : ℝ))
    (B := ((6900737892159197/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504229159559/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895054846075361/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611881619297 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504229159559 : ℝ)) (s := (0.863569889848 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613810314888 : ℝ) ≤ 0.687572500018 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613810314888 : ℝ)) (Q := (0.613810314888 : ℝ))
      (s := (0.789453543496 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782477299579 : ℝ)) (R := (0.783016459424 : ℝ)) (Q2 := (0.613810314888 : ℝ)) (T := (0.829669847571 : ℝ))
    (B := ((6895054846075361/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503036798211/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1722344526152283/2500000000000000) := by
  have hk1 : kappa q ≤ 0.611084046364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503036798211 : ℝ)) (s := (0.864264993880 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613011286795 : ℝ) ≤ 0.687002778010 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613011286795 : ℝ)) (Q := (0.613011286795 : ℝ))
      (s := (0.790074149851 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781967487446 : ℝ)) (R := (0.782506647291 : ℝ)) (Q2 := (0.613011286795 : ℝ)) (T := (0.829326044460 : ℝ))
    (B := ((1722344526152283/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501844436863/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (688370765767593/1000000000000000) := by
  have hk1 : kappa q ≤ 0.610287012813 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501844436863 : ℝ)) (s := (0.864957895617 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612212798710 : ℝ) ≤ 0.686433712838 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612212798710 : ℝ)) (Q := (0.612212798710 : ℝ))
      (s := (0.790693043536 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781457687832 : ℝ)) (R := (0.781996847677 : ℝ)) (Q2 := (0.612212798710 : ℝ)) (T := (0.828982495384 : ℝ))
    (B := ((688370765767593/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250326037757/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6878043495229499/10000000000000000) := by
  have hk1 : kappa q ≤ 0.609490518047 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500652075514 : ℝ)) (s := (0.865648600348 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611414850035 : ℝ) ≤ 0.685865303287 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611414850035 : ℝ)) (Q := (0.611414850035 : ℝ))
      (s := (0.791310230667 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780947900379 : ℝ)) (R := (0.781487060224 : ℝ)) (Q2 := (0.611414850035 : ℝ)) (T := (0.828639199924 : ℝ))
    (B := ((6878043495229499/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249729857083/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6872385607261677/10000000000000000) := by
  have hk1 : kappa q ≤ 0.608694561471 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499459714166 : ℝ)) (s := (0.866337113326 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610617440173 : ℝ) ≤ 0.685297548147 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610617440173 : ℝ)) (Q := (0.610617440173 : ℝ))
      (s := (0.791925717323 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780438124729 : ℝ)) (R := (0.780977284574 : ℝ)) (Q2 := (0.610617440173 : ℝ)) (T := (0.828296157665 : ℝ))
    (B := ((6872385607261677/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249133676409/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (686673398380217/1000000000000000) := by
  have hk1 : kappa q ≤ 0.607899142493 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498267352818 : ℝ)) (s := (0.867023439773 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609820568532 : ℝ) ≤ 0.684730446211 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609820568532 : ℝ)) (Q := (0.609820568532 : ℝ))
      (s := (0.792539509549 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779928360526 : ℝ)) (R := (0.780467520371 : ℝ)) (Q2 := (0.609820568532 : ℝ)) (T := (0.827953368190 : ℝ))
    (B := ((686673398380217/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49707499147/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (274443544596733/400000000000000) := by
  have hk1 : kappa q ≤ 0.607104260526 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497074991470 : ℝ)) (s := (0.867707584879 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609024234521 : ℝ) ≤ 0.684163996278 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609024234521 : ℝ)) (Q := (0.609024234521 : ℝ))
      (s := (0.793151613355 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779418607415 : ℝ)) (R := (0.779957767260 : ℝ)) (Q2 := (0.609024234521 : ℝ)) (T := (0.827610831088 : ℝ))
    (B := ((274443544596733/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247941315061/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3427724745357453/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606309914984 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495882630122 : ℝ)) (s := (0.868389553797 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608228437556 : ℝ) ≤ 0.683598197151 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608228437556 : ℝ)) (Q := (0.608228437556 : ℝ))
      (s := (0.793762034711 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778908865043 : ℝ)) (R := (0.779448024888 : ℝ)) (Q2 := (0.608228437556 : ℝ)) (T := (0.827268545949 : ℝ))
    (B := ((3427724745357453/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247345134387/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1712454150333469/2500000000000000) := by
  have hk1 : kappa q ≤ 0.605516105285 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494690268774 : ℝ)) (s := (0.869069351652 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607433177054 : ℝ) ≤ 0.683033047640 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607433177054 : ℝ)) (Q := (0.607433177054 : ℝ))
      (s := (0.794370779558 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778399133057 : ℝ)) (R := (0.778938292902 : ℝ)) (Q2 := (0.607433177054 : ℝ)) (T := (0.826926512363 : ℝ))
    (B := ((1712454150333469/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246748953713/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1711047484238543/2500000000000000) := by
  have hk1 : kappa q ≤ 0.604722830850 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493497907426 : ℝ)) (s := (0.869746983534 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606638452434 : ℝ) ≤ 0.682468546552 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606638452434 : ℝ)) (Q := (0.606638452434 : ℝ))
      (s := (0.794977853798 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777889411105 : ℝ)) (R := (0.778428570950 : ℝ)) (Q2 := (0.606638452434 : ℝ)) (T := (0.826584729923 : ℝ))
    (B := ((1711047484238543/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246152773039/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838569487791489/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603930091102 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492305546078 : ℝ)) (s := (0.870422454502 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605844263117 : ℝ) ≤ 0.681904692704 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605844263117 : ℝ)) (Q := (0.605844263117 : ℝ))
      (s := (0.795583263304 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777379698835 : ℝ)) (R := (0.777918858680 : ℝ)) (Q2 := (0.605844263117 : ℝ)) (T := (0.826243198222 : ℝ))
    (B := ((6838569487791489/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49111318473/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1708238811024517/2500000000000000) := by
  have hk1 : kappa q ≤ 0.603137885470 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491113184730 : ℝ)) (s := (0.871095769583 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605050608534 : ℝ) ≤ 0.681341484917 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605050608534 : ℝ)) (Q := (0.605050608534 : ℝ))
      (s := (0.796187013907 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776869995900 : ℝ)) (R := (0.777409155745 : ℝ)) (Q2 := (0.605050608534 : ℝ)) (T := (0.825901916856 : ℝ))
    (B := ((1708238811024517/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244960411691/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827347196162473/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602346213384 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489920823382 : ℝ)) (s := (0.871766933772 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604257488111 : ℝ) ≤ 0.680778922015 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604257488111 : ℝ)) (Q := (0.604257488111 : ℝ))
      (s := (0.796789111411 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776360301950 : ℝ)) (R := (0.776899461795 : ℝ)) (Q2 := (0.604257488111 : ℝ)) (T := (0.825560885424 : ℝ))
    (B := ((6827347196162473/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (244364231017/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3410872667154693/5000000000000000) := by
  have hk1 : kappa q ≤ 0.601555074275 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488728462034 : ℝ)) (s := (0.872435952032 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603464901278 : ℝ) ≤ 0.680217002823 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603464901278 : ℝ)) (Q := (0.603464901278 : ℝ))
      (s := (0.797389561586 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775850616636 : ℝ)) (R := (0.776389776481 : ℝ)) (Q2 := (0.603464901278 : ℝ)) (T := (0.825220103522 : ℝ))
    (B := ((3410872667154693/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243768050343/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816149648899393/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600764467582 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487536100686 : ℝ)) (s := (0.873102829298 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602672847474 : ℝ) ≤ 0.679655726177 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602672847474 : ℝ)) (Q := (0.602672847474 : ℝ))
      (s := (0.797988370165 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775340939614 : ℝ)) (R := (0.775880099459 : ℝ)) (Q2 := (0.602672847474 : ℝ)) (T := (0.824879570754 : ℝ))
    (B := ((6816149648899393/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243171869669/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (851320016291097/1250000000000000) := by
  have hk1 : kappa q ≤ 0.599974392744 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486343739338 : ℝ)) (s := (0.873767570471 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601881326138 : ℝ) ≤ 0.679095090914 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601881326138 : ℝ)) (Q := (0.601881326138 : ℝ))
      (s := (0.798585542849 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774831270538 : ℝ)) (R := (0.775370430383 : ℝ)) (Q2 := (0.601881326138 : ℝ)) (T := (0.824539286721 : ℝ))
    (B := ((851320016291097/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48515137799/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3402488384514651/5000000000000000) := by
  have hk1 : kappa q ≤ 0.599184849202 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485151377990 : ℝ)) (s := (0.874430180423 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601090336708 : ℝ) ≤ 0.678535095872 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601090336708 : ℝ)) (Q := (0.601090336708 : ℝ))
      (s := (0.799181085310 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774321609063 : ℝ)) (R := (0.774860768908 : ℝ)) (Q2 := (0.601090336708 : ℝ)) (T := (0.824199251027 : ℝ))
    (B := ((3402488384514651/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241979508321/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (849924944433503/1250000000000000) := by
  have hk1 : kappa q ≤ 0.598395836404 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483959016642 : ℝ)) (s := (0.875090663995 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600299878631 : ℝ) ≤ 0.677975739898 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600299878631 : ℝ)) (Q := (0.600299878631 : ℝ))
      (s := (0.799775003183 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773811954846 : ℝ)) (R := (0.774351114691 : ℝ)) (Q2 := (0.600299878631 : ℝ)) (T := (0.823859463278 : ℝ))
    (B := ((849924944433503/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241383327647/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793828480147071/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597607353797 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482766655294 : ℝ)) (s := (0.875749025998 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599509951356 : ℝ) ≤ 0.677417021844 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599509951356 : ℝ)) (Q := (0.599509951356 : ℝ))
      (s := (0.800367302072 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773302307546 : ℝ)) (R := (0.773841467391 : ℝ)) (Q2 := (0.599509951356 : ℝ)) (T := (0.823519923084 : ℝ))
    (B := ((6793828480147071/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96314858789/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3394131520764079/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596819400833 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481574293945 : ℝ)) (s := (0.876405271214 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598720554331 : ℝ) ≤ 0.676858940560 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598720554331 : ℝ)) (Q := (0.598720554331 : ℝ))
      (s := (0.800957987551 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772792666821 : ℝ)) (R := (0.773331826666 : ℝ)) (Q2 := (0.598720554331 : ℝ)) (T := (0.823180630051 : ℝ))
    (B := ((3394131520764079/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480381932597/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3391351527788719/5000000000000000) := by
  have hk1 : kappa q ≤ 0.596031976968 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480381932597 : ℝ)) (s := (0.877059404394 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597931687013 : ℝ) ≤ 0.676301494907 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597931687013 : ℝ)) (Q := (0.597931687013 : ℝ))
      (s := (0.801547065160 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772283032332 : ℝ)) (R := (0.772822192177 : ℝ)) (Q2 := (0.597931687013 : ℝ)) (T := (0.822841583792 : ℝ))
    (B := ((3391351527788719/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479189571249/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (135542983642427/200000000000000) := by
  have hk1 : kappa q ≤ 0.595245081658 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479189571249 : ℝ)) (s := (0.877711430259 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597143348854 : ℝ) ≤ 0.675744683744 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597143348854 : ℝ)) (Q := (0.597143348854 : ℝ))
      (s := (0.802134540411 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771773403738 : ℝ)) (R := (0.772312563583 : ℝ)) (Q2 := (0.597143348854 : ℝ)) (T := (0.822502783918 : ℝ))
    (B := ((135542983642427/200000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12850 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477997209901/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1692900352948659/2500000000000000) := by
  have hk1 : kappa q ≤ 0.594458714366 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477997209901 : ℝ)) (s := (0.878361353503 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596355539320 : ℝ) ≤ 0.675188505942 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596355539320 : ℝ)) (Q := (0.596355539320 : ℝ))
      (s := (0.802720418778 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771263780704 : ℝ)) (R := (0.771802940549 : ℝ)) (Q2 := (0.596355539320 : ℝ)) (T := (0.822164230046 : ℝ))
    (B := ((1692900352948659/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S20
namespace BstLean.Part269.S20
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12850 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052173772998 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S20.wn_upper (by omega : 12850 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010535112313 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035597771358)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010535112313 + 2 * 0.737676 / 12850) := by gcongr
    _ ≤ (0.052173772998 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12850 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12850 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.357840487546 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12850 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (113.357840487546 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12850 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003364259073 + 0.003253885827 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003364259073 + 0.003253885827 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 113.357840487546 ≤ R)
    (hB : (X + 0.052173772998 + R + 0.008431564502) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008431564502 := by
    convert (BstLean.Part269.S20.finite_centre_upper (by omega : 12850 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (42499158693/500000000000)
  | 2 => (5370773103/62500000000)
  | 3 => (86863348659/1000000000000)
  | 4 => (2194809733/25000000000)
  | 5 => (88720873063/1000000000000)
  | 6 => (44825232787/500000000000)
  | 7 => (90583158269/1000000000000)
  | 8 => (45760656801/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003364259073 + 0.003253885827 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218689201429 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010902355526 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003364259073 + 0.003253885827 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220262065337 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011016649825 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003364259073 + 0.003253885827 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.221814357132 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011130566620 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003364259073 + 0.003253885827 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223346288004 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011244114186 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003364259073 + 0.003253885827 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.224858063774 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011357300561 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003364259073 + 0.003253885827 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226349883422 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011470133437 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003364259073 + 0.003253885827 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.227821940966 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011582620295 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12850 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003364259073 + 0.003253885827 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229274424014 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011694768297 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12850 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g) :
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

end BstLean.Part269.S20

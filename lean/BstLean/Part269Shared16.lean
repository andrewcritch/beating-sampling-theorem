import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S16
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12750 ≤ n) : wn n ≤ 1.035738320912 := by
  have hnR : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (112.915897906362 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (112.915897906362 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.035738320912 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12750 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12750 + 24 / (12750 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12750 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008464706508 : ℝ) := by
  have hnR : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (112.915897906362 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12750 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.035738320912 * (81 / 1000 / 12750)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.035738320912 * n *
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
        4 * (1 / 2.506628) * 1.035738320912 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035738320912 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.035738320912 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12750)) / 112.915897906362 := by gcongr
    _ ≤ (0.008464706508 : ℝ) := by norm_num

end BstLean.Part269.S16
namespace BstLean.Part269.S16
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12750 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12750 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12750 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12750 + 0.008464706508 / 112.915897906362) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12750 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12750 := by gcongr
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
  have hn : (112.915897906362 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S16.finite_centre_upper (by omega : 12750 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528065841903/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (876265418257707/1250000000000000) := by
  have hk1 : kappa q ≤ 0.627940143796 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528065841903 : ℝ)) (s := (0.849203430643 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629907836104 : ℝ) ≤ 0.699108660285 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629907836104 : ℝ)) (Q := (0.629907836104 : ℝ))
      (s := (0.776669889989 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792674145320 : ℝ)) (R := (0.793217533870 : ℝ)) (Q2 := (0.629907836104 : ℝ)) (T := (0.836601037355 : ℝ))
    (B := ((876265418257707/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526872426093/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7004313258494501/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627130943083 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526872426093 : ℝ)) (s := (0.849944378547 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629097161880 : ℝ) ≤ 0.698525024334 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629097161880 : ℝ)) (Q := (0.629097161880 : ℝ))
      (s := (0.777326675803 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792163556311 : ℝ)) (R := (0.792706944861 : ℝ)) (Q2 := (0.629097161880 : ℝ)) (T := (0.836251755177 : ℝ))
    (B := ((7004313258494501/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (525679010283/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6998509686415799/10000000000000000) := by
  have hk1 : kappa q ≤ 0.626322295326 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525679010283 : ℝ)) (s := (0.850683006853 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628287041260 : ℝ) ≤ 0.697942071571 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628287041260 : ℝ)) (Q := (0.628287041260 : ℝ))
      (s := (0.777981615326 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791652987230 : ℝ)) (R := (0.792196375780 : ℝ)) (Q2 := (0.628287041260 : ℝ)) (T := (0.835902736168 : ℝ))
    (B := ((6998509686415799/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (524485594473/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6992712618937441/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625514199863 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524485594473 : ℝ)) (s := (0.851419321598 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627477473582 : ℝ) ≤ 0.697359800698 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477473582 : ℝ)) (Q := (0.627477473582 : ℝ))
      (s := (0.778634715478 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791142437698 : ℝ)) (R := (0.791685826248 : ℝ)) (Q2 := (0.627477473582 : ℝ)) (T := (0.835553979880 : ℝ))
    (B := ((6992712618937441/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523292178663/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6986922045214551/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624706656037 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523292178663 : ℝ)) (s := (0.852153328780 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668458187 : ℝ) ≤ 0.696778210418 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668458187 : ℝ)) (Q := (0.626668458187 : ℝ))
      (s := (0.779285983137 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790631907338 : ℝ)) (R := (0.791175295888 : ℝ)) (Q2 := (0.626668458187 : ℝ)) (T := (0.835205485865 : ℝ))
    (B := ((6986922045214551/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261049381427/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1396227590889043/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623899663193 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522098762854 : ℝ)) (s := (0.852885034355 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625859994420 : ℝ) ≤ 0.696197299442 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625859994420 : ℝ)) (Q := (0.625859994420 : ℝ))
      (s := (0.779935425138 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790121395772 : ℝ)) (R := (0.790664784322 : ℝ)) (Q2 := (0.625859994420 : ℝ)) (T := (0.834857253677 : ℝ))
    (B := ((1396227590889043/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130226336761/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1395072067174043/2000000000000000) := by
  have hk1 : kappa q ≤ 0.623093220678 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520905347044 : ℝ)) (s := (0.853614444244 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625052081626 : ℝ) ≤ 0.695617066480 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625052081626 : ℝ)) (Q := (0.625052081626 : ℝ))
      (s := (0.780583048276 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789610902623 : ℝ)) (R := (0.790154291173 : ℝ)) (Q2 := (0.625052081626 : ℝ)) (T := (0.834509282871 : ℝ))
    (B := ((1395072067174043/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259855965617/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1742397294693189/2500000000000000) := by
  have hk1 : kappa q ≤ 0.622287327844 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519711931234 : ℝ)) (s := (0.854341564325 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624244719157 : ℝ) ≤ 0.695037510250 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624244719157 : ℝ)) (Q := (0.624244719157 : ℝ))
      (s := (0.781228859301 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789100427517 : ℝ)) (R := (0.789643816067 : ℝ)) (Q2 := (0.624244719157 : ℝ)) (T := (0.834161573006 : ℝ))
    (B := ((1742397294693189/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16203703607/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392764894495641/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621481984045 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518518515424 : ℝ)) (s := (0.855066400441 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623437906365 : ℝ) ≤ 0.694458629471 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623437906365 : ℝ)) (Q := (0.623437906365 : ℝ))
      (s := (0.781872864926 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788589970079 : ℝ)) (R := (0.789133358629 : ℝ)) (Q2 := (0.623437906365 : ℝ)) (T := (0.833814123637 : ℝ))
    (B := ((1392764894495641/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258662549807/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958066206353831/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620677188639 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517325099614 : ℝ)) (s := (0.855788958395 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622631642606 : ℝ) ≤ 0.693880422869 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622631642606 : ℝ)) (Q := (0.622631642606 : ℝ))
      (s := (0.782515071821 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788079529935 : ℝ)) (R := (0.788622918485 : ℝ)) (Q2 := (0.622631642606 : ℝ)) (T := (0.833466934327 : ℝ))
    (B := ((6958066206353831/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103226336761/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3476157184904269/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619872940986 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516131683805 : ℝ)) (s := (0.856509243951 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621825927241 : ℝ) ≤ 0.693302889172 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621825927241 : ℝ)) (Q := (0.621825927241 : ℝ))
      (s := (0.783155486613 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787569106714 : ℝ)) (R := (0.788112495264 : ℝ)) (Q2 := (0.621825927241 : ℝ)) (T := (0.833120004635 : ℝ))
    (B := ((3476157184904269/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102987653599/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3473284476146307/5000000000000000) := by
  have hk1 : kappa q ≤ 0.619069240449 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514938267995 : ℝ)) (s := (0.857227262839 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621020759629 : ℝ) ≤ 0.692726027112 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621020759629 : ℝ)) (Q := (0.621020759629 : ℝ))
      (s := (0.783794115894 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787058700042 : ℝ)) (R := (0.787602088592 : ℝ)) (Q2 := (0.621020759629 : ℝ)) (T := (0.832773334124 : ℝ))
    (B := ((3473284476146307/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102748970437/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6940829943297471/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618266086395 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513744852185 : ℝ)) (s := (0.857943020750 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620216139140 : ℝ) ≤ 0.692149835428 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620216139140 : ℝ)) (Q := (0.620216139140 : ℝ))
      (s := (0.784430966211 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786548309552 : ℝ)) (R := (0.787091698102 : ℝ)) (Q2 := (0.620216139140 : ℝ)) (T := (0.832426922360 : ℝ))
    (B := ((6940829943297471/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (4100411491/8000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3467548666177697/5000000000000000) := by
  have hk1 : kappa q ≤ 0.617463478195 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512551436375 : ℝ)) (s := (0.858656523338 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619412065138 : ℝ) ≤ 0.691574312858 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619412065138 : ℝ)) (Q := (0.619412065138 : ℝ))
      (s := (0.785066044077 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786037934872 : ℝ)) (R := (0.786581323422 : ℝ)) (Q2 := (0.619412065138 : ℝ)) (T := (0.832080768906 : ℝ))
    (B := ((3467548666177697/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102271604113/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (866171388629911/1250000000000000) := by
  have hk1 : kappa q ≤ 0.616661415220 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511358020565 : ℝ)) (s := (0.859367776220 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618608536999 : ℝ) ≤ 0.690999458150 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618608536999 : ℝ)) (Q := (0.618608536999 : ℝ))
      (s := (0.785699355958 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785527575635 : ℝ)) (R := (0.786070964185 : ℝ)) (Q2 := (0.618608536999 : ℝ)) (T := (0.831734873332 : ℝ))
    (B := ((866171388629911/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127541151189/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27045512745947/39062500000000) := by
  have hk1 : kappa q ≤ 0.615859896847 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510164604756 : ℝ)) (s := (0.860076784976 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617805554097 : ℝ) ≤ 0.690425270052 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617805554097 : ℝ)) (Q := (0.617805554097 : ℝ))
      (s := (0.786330908287 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785017231474 : ℝ)) (R := (0.785560620024 : ℝ)) (Q2 := (0.617805554097 : ℝ)) (T := (0.831389235205 : ℝ))
    (B := ((27045512745947/39062500000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (254485594473/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1729484445944557/2500000000000000) := by
  have hk1 : kappa q ≤ 0.615058922454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508971188946 : ℝ)) (s := (0.860783555154 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617003115805 : ℝ) ≤ 0.689851747316 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617003115805 : ℝ)) (Q := (0.617003115805 : ℝ))
      (s := (0.786960707461 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784506902020 : ℝ)) (R := (0.785050290570 : ℝ)) (Q2 := (0.617003115805 : ℝ)) (T := (0.831043854096 : ℝ))
    (B := ((1729484445944557/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31736110821/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3456115330589981/5000000000000000) := by
  have hk1 : kappa q ≤ 0.614258491423 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507777773136 : ℝ)) (s := (0.861488092262 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616201221509 : ℝ) ≤ 0.689278888701 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616201221509 : ℝ)) (Q := (0.616201221509 : ℝ))
      (s := (0.787588759831 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783996586910 : ℝ)) (R := (0.784539975460 : ℝ)) (Q2 := (0.616201221509 : ℝ)) (T := (0.830698729577 : ℝ))
    (B := ((3456115330589981/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253292178663/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1381305976980111/2000000000000000) := by
  have hk1 : kappa q ≤ 0.613458603141 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506584357326 : ℝ)) (s := (0.862190401775 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615399870592 : ℝ) ≤ 0.688706692968 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615399870592 : ℝ)) (Q := (0.615399870592 : ℝ))
      (s := (0.788215071713 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783486285779 : ℝ)) (R := (0.784029674329 : ℝ)) (Q2 := (0.615399870592 : ℝ)) (T := (0.830353861220 : ℝ))
    (B := ((1381305976980111/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (126347735379/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6900835444712327/10000000000000000) := by
  have hk1 : kappa q ≤ 0.612659256996 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505390941516 : ℝ)) (s := (0.862890489132 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614599062443 : ℝ) ≤ 0.688135158886 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614599062443 : ℝ)) (Q := (0.614599062443 : ℝ))
      (s := (0.788839649387 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782975998265 : ℝ)) (R := (0.783519386815 : ℝ)) (Q2 := (0.614599062443 : ℝ)) (T := (0.830009248603 : ℝ))
    (B := ((6900835444712327/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504197525707/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3447573665213379/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611860452378 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504197525707 : ℝ)) (s := (0.863588359736 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613798796449 : ℝ) ≤ 0.687564285221 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613798796449 : ℝ)) (Q := (0.613798796449 : ℝ))
      (s := (0.789462499096 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782465724004 : ℝ)) (R := (0.783009112554 : ℝ)) (Q2 := (0.613798796449 : ℝ)) (T := (0.829664891301 : ℝ))
    (B := ((3447573665213379/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503004109897/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (27557862127577/40000000000000) := by
  have hk1 : kappa q ≤ 0.611062188683 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503004109897 : ℝ)) (s := (0.864284018959 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612999072006 : ℝ) ≤ 0.686994070749 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612999072006 : ℝ)) (Q := (0.612999072006 : ℝ))
      (s := (0.790083627042 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781955462636 : ℝ)) (R := (0.782498851186 : ℝ)) (Q2 := (0.612999072006 : ℝ)) (T := (0.829320788891 : ℝ))
    (B := ((27557862127577/40000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501810694087/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3441895019501947/5000000000000000) := by
  have hk1 : kappa q ≤ 0.610264465308 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501810694087 : ℝ)) (s := (0.864977472135 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612199888509 : ℝ) ≤ 0.686424514248 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612199888509 : ℝ)) (Q := (0.612199888509 : ℝ))
      (s := (0.790703039396 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781445213800 : ℝ)) (R := (0.781988602350 : ℝ)) (Q2 := (0.612199888509 : ℝ)) (T := (0.828976940955 : ℝ))
    (B := ((3441895019501947/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (500617278277/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439060420841619/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609467281654 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500617278277 : ℝ)) (s := (0.865668724566 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611401245360 : ℝ) ≤ 0.685855614503 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611401245360 : ℝ)) (Q := (0.611401245360 : ℝ))
      (s := (0.791320742287 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780934977138 : ℝ)) (R := (0.781478365688 : ℝ)) (Q2 := (0.611401245360 : ℝ)) (T := (0.828633347074 : ℝ))
    (B := ((3439060420841619/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499423862467/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3436228964949027/5000000000000000) := by
  have hk1 : kappa q ≤ 0.608670637125 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499423862467 : ℝ)) (s := (0.866357781520 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610603141959 : ℝ) ≤ 0.685287370297 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610603141959 : ℝ)) (Q := (0.610603141959 : ℝ))
      (s := (0.791936741811 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780424752291 : ℝ)) (R := (0.780968140841 : ℝ)) (Q2 := (0.610603141959 : ℝ)) (T := (0.828290006829 : ℝ))
    (B := ((3436228964949027/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249115223329/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3433400646826057/5000000000000000) := by
  have hk1 : kappa q ≤ 0.607874531129 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498230446658 : ℝ)) (s := (0.867044648230 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609805577715 : ℝ) ≤ 0.684719780426 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609805577715 : ℝ)) (Q := (0.609805577715 : ℝ))
      (s := (0.792551044027 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779914538903 : ℝ)) (R := (0.780457927453 : ℝ)) (Q2 := (0.609805577715 : ℝ)) (T := (0.827946919808 : ℝ))
    (B := ((3433400646826057/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (7766203607/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (85764386537337/125000000000000) := by
  have hk1 : kappa q ≤ 0.607078963074 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497037030848 : ℝ)) (s := (0.867729329899 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609008552034 : ℝ) ≤ 0.684152843681 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609008552034 : ℝ)) (Q := (0.609008552034 : ℝ))
      (s := (0.793163654960 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779404336617 : ℝ)) (R := (0.779947725167 : ℝ)) (Q2 := (0.609008552034 : ℝ)) (T := (0.827604085595 : ℝ))
    (B := ((85764386537337/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247921807519/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (85693835099771/125000000000000) := by
  have hk1 : kappa q ≤ 0.606283932375 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495843615038 : ℝ)) (s := (0.868411831694 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608212064331 : ℝ) ≤ 0.683586558866 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608212064331 : ℝ)) (Q := (0.608212064331 : ℝ))
      (s := (0.793774580598 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778894145079 : ℝ)) (R := (0.779437533629 : ℝ)) (Q2 := (0.608212064331 : ℝ)) (T := (0.827261503780 : ℝ))
    (B := ((85693835099771/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123662549807/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3424934469376343/5000000000000000) := by
  have hk1 : kappa q ≤ 0.605489438448 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494650199228 : ℝ)) (s := (0.869092158752 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607416114019 : ℝ) ≤ 0.683020924780 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607416114019 : ℝ)) (Q := (0.607416114019 : ℝ))
      (s := (0.794383826894 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778383963935 : ℝ)) (R := (0.778927352485 : ℝ)) (Q2 := (0.607416114019 : ℝ)) (T := (0.826919173949 : ℝ))
    (B := ((3424934469376343/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246728391709/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3422118652726747/5000000000000000) := by
  have hk1 : kappa q ≤ 0.604695480712 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493456783418 : ℝ)) (s := (0.869770316175 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606620700518 : ℝ) ≤ 0.682455940236 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606620700518 : ℝ)) (Q := (0.606620700518 : ℝ))
      (s := (0.794991399767 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777873792832 : ℝ)) (R := (0.778417181382 : ℝ)) (Q2 := (0.606620700518 : ℝ)) (T := (0.826577095698 : ℝ))
    (B := ((3422118652726747/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492263367609/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (854826487284313/1250000000000000) := by
  have hk1 : kappa q ≤ 0.603902058592 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492263367609 : ℝ)) (s := (0.870446309034 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605825823252 : ℝ) ≤ 0.681891604046 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605825823252 : ℝ)) (Q := (0.605825823252 : ℝ))
      (s := (0.795597305100 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777363631421 : ℝ)) (R := (0.777907019971 : ℝ)) (Q2 := (0.605825823252 : ℝ)) (T := (0.826235268619 : ℝ))
    (B := ((854826487284313/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491069951799/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6832992707442783/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603109171511 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491069951799 : ℝ)) (s := (0.871120142369 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605031481642 : ℝ) ≤ 0.681327915024 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605031481642 : ℝ)) (Q := (0.605031481642 : ℝ))
      (s := (0.796201548744 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776853479348 : ℝ)) (R := (0.777396867898 : ℝ)) (Q2 := (0.605031481642 : ℝ)) (T := (0.825893692304 : ℝ))
    (B := ((6832992707442783/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489876535989/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (853422465402731/1250000000000000) := by
  have hk1 : kappa q ≤ 0.602316818898 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489876535989 : ℝ)) (s := (0.871791821187 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604237675114 : ℝ) ≤ 0.680764871992 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604237675114 : ℝ)) (Q := (0.604237675114 : ℝ))
      (s := (0.796804136519 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776343336264 : ℝ)) (R := (0.776886724814 : ℝ)) (Q2 := (0.604237675114 : ℝ)) (T := (0.825552366352 : ℝ))
    (B := ((853422465402731/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488683120179/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (213180404247233/312500000000000) := by
  have hk1 : kappa q ≤ 0.601525000186 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488683120179 : ℝ)) (s := (0.872461350464 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603444403104 : ℝ) ≤ 0.680202473776 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603444403104 : ℝ)) (Q := (0.603444403104 : ℝ))
      (s := (0.797405074202 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775833201822 : ℝ)) (R := (0.776376590372 : ℝ)) (Q2 := (0.603444403104 : ℝ)) (T := (0.825211290360 : ℝ))
    (B := ((213180404247233/312500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487489704369/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816172335847391/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600733714811 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487489704369 : ℝ)) (s := (0.873128735145 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602651665044 : ℝ) ≤ 0.679640719207 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602651665044 : ℝ)) (Q := (0.602651665044 : ℝ))
      (s := (0.798004367545 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775323075675 : ℝ)) (R := (0.775866464225 : ℝ)) (Q2 := (0.602651665044 : ℝ)) (T := (0.824870463929 : ℝ))
    (B := ((6816172335847391/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (6078703607/12500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702644478350313/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599942962209 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486296288560 : ℝ)) (s := (0.873793980143 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601859460371 : ℝ) ≤ 0.679079607116 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601859460371 : ℝ)) (Q := (0.601859460371 : ℝ))
      (s := (0.798602022263 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774812957476 : ℝ)) (R := (0.775356346026 : ℝ)) (Q2 := (0.601859460371 : ℝ)) (T := (0.824529886659 : ℝ))
    (B := ((1702644478350313/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1940411491/4000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6804989658980247/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599152741823 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485102872750 : ℝ)) (s := (0.874457090343 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601067788525 : ℝ) ≤ 0.678519136343 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601067788525 : ℝ)) (Q := (0.601067788525 : ℝ))
      (s := (0.799198044041 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774302846880 : ℝ)) (R := (0.774846235430 : ℝ)) (Q2 := (0.601067788525 : ℝ)) (T := (0.824189558154 : ℝ))
    (B := ((6804989658980247/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (24195472847/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1359881512605397/2000000000000000) := by
  have hk1 : kappa q ≤ 0.598363053095 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483909456940 : ℝ)) (s := (0.875118070597 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600276648948 : ℝ) ≤ 0.677959305729 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600276648948 : ℝ)) (Q := (0.600276648948 : ℝ))
      (s := (0.799792438529 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773792743542 : ℝ)) (R := (0.774336132092 : ℝ)) (Q2 := (0.600276648948 : ℝ)) (T := (0.823849478019 : ℝ))
    (B := ((1359881512605397/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48271604113/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3396915808009637/5000000000000000) := by
  have hk1 : kappa q ≤ 0.597573895474 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482716041130 : ℝ)) (s := (0.875776925727 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599486041089 : ℝ) ≤ 0.677400114123 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599486041089 : ℝ)) (Q := (0.599486041089 : ℝ))
      (s := (0.800385211345 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773282647120 : ℝ)) (R := (0.773826035670 : ℝ)) (Q2 := (0.599486041089 : ℝ)) (T := (0.823509645860 : ℝ))
    (B := ((3396915808009637/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12038065633/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1697065380821763/2500000000000000) := by
  have hk1 : kappa q ≤ 0.596785268411 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481522625320 : ℝ)) (s := (0.876433660528 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598695964397 : ℝ) ≤ 0.676841560374 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598695964397 : ℝ)) (Q := (0.598695964397 : ℝ))
      (s := (0.800976368076 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772772557273 : ℝ)) (R := (0.773315945823 : ℝ)) (Q2 := (0.598695964397 : ℝ)) (T := (0.823170061287 : ℝ))
    (B := ((1697065380821763/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480329209511/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782696672909247/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595997171359 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480329209511 : ℝ)) (s := (0.877088279759 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597906418323 : ℝ) ≤ 0.676283643338 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597906418323 : ℝ)) (Q := (0.597906418323 : ℝ))
      (s := (0.801565914276 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772262473659 : ℝ)) (R := (0.772805862209 : ℝ)) (Q2 := (0.597906418323 : ℝ)) (T := (0.822830723909 : ℝ))
    (B := ((6782696672909247/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479135793701/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777137945691933/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595209603775 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479135793701 : ℝ)) (s := (0.877740788158 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597117402326 : ℝ) ≤ 0.675726361876 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597117402326 : ℝ)) (Q := (0.597117402326 : ℝ))
      (s := (0.802153855467 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771752395940 : ℝ)) (R := (0.772295784490 : ℝ)) (Q2 := (0.597117402326 : ℝ)) (T := (0.822491633338 : ℝ))
    (B := ((6777137945691933/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12750 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477942377891/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1692896333061479/2500000000000000) := by
  have hk1 : kappa q ≤ 0.594422565116 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477942377891 : ℝ)) (s := (0.878391190425 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596328915857 : ℝ) ≤ 0.675169714846 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596328915857 : ℝ)) (Q := (0.596328915857 : ℝ))
      (s := (0.802740197146 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771242323773 : ℝ)) (R := (0.771785712323 : ℝ)) (Q2 := (0.596328915857 : ℝ)) (T := (0.822152789186 : ℝ))
    (B := ((1692896333061479/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S16
namespace BstLean.Part269.S16
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12750 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052380186479 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S16.wn_upper (by omega : 12750 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010576345787 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035738320912)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010576345787 + 2 * 0.737676 / 12750) := by gcongr
    _ ≤ (0.052380186479 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12750 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12750 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.915897906362 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12750 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (112.915897906362 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12750 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003465461536 + 0.003280300441 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003465461536 + 0.003280300441 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 112.915897906362 ≤ R)
    (hB : (X + 0.052380186479 + R + 0.008464706508) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008464706508 := by
    convert (BstLean.Part269.S16.finite_centre_upper (by omega : 12750 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (42638672917/500000000000)
  | 2 => (86216248297/1000000000000)
  | 3 => (17430547947/200000000000)
  | 4 => (44044055313/500000000000)
  | 5 => (2225598149/25000000000)
  | 6 => (89962066537/1000000000000)
  | 7 => (18180954851/200000000000)
  | 8 => (9185470143/100000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003465461536 + 0.003280300441 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.218949081294 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010945026356 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003465461536 + 0.003280300441 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.220520522629 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011059767993 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003465461536 + 0.003280300441 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222071435805 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011174130648 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003465461536 + 0.003280300441 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.223602030472 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011288122628 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003465461536 + 0.003280300441 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225112510996 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011401752005 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003465461536 + 0.003280300441 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.226603074966 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011515026499 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003465461536 + 0.003280300441 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228073915082 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011627953620 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12750 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003465461536 + 0.003280300441 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.229525217695 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011740540559 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12750 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g) :
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

end BstLean.Part269.S16

import BstLean.Part253CentreFormula
import BstLean.Part253EnergyUpper
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264EnergyLower
import BstLean.Part264FiniteCentre

/-! A uniform finite-centre bound at the original program length J = n. -/
namespace BstLean.Part269.S7
open Real
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upper {n : ℕ} (hn : 12525 ≤ n) : wn n ≤ 1.036060725407 := by
  have hnR : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (111.915146427996 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold wn
  calc
    _ ≤ (1 + 2 / (111.915146427996 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036060725407 : ℝ) := by norm_num

theorem deltaChi_upper {n : ℕ} (hn : 12525 ≤ n) : deltaChi n 12 ≤ 0.0005669 := by
  have hnR : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold deltaChi
  calc
    _ ≤ 2 * (3.464102 : ℝ) / 12525 + 24 / (12525 : ℝ)^2 := by gcongr <;> norm_num
    _ ≤ (0.0005669 : ℝ) := by norm_num

theorem finite_centre_upper {n : ℕ} (hn : 12525 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008540726171 : ℝ) := by
  have hnR : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnr : (111.915146427996 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
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
  have hbmax : betaJ n ≤ 81 / 1000 / (12525 : ℝ) := by
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      1.421981 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036060725407 * (81 / 1000 / 12525)) * n := by gcongr
      _ ≤ _ := by rw [mul_pow, sq_sqrt hn0]; norm_num [div_eq_mul_inv] <;> nlinarith
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ 1.62763 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036060725407 * n *
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
        4 * (1 / 2.506628) * 1.036060725407 * (0.878679 * √(n : ℝ)) *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by
      unfold finiteEnergy epsJ
      gcongr
    _ = (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036060725407 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / n)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ (1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
        4 * (1 / 2.506628) * 1.036060725407 * 0.878679 *
          (81 / 1000 + (1792 / 10000) ^ 2 / 12525)) / 111.915146427996 := by gcongr
    _ ≤ (0.008540726171 : ℝ) := by norm_num

end BstLean.Part269.S7
namespace BstLean.Part269.S7
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12525 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12525 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12525 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12525 + 0.008540726171 / 111.915146427996) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12525 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12525 := by gcongr
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
  have hn : (111.915146427996 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part269.S7.finite_centre_upper (by omega : 12525 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (26402082393/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3505288250529217/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627923733426 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528041647860 : ℝ)) (s := (0.849218474909 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629913956902 : ℝ) ≤ 0.699113067971 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629913956902 : ℝ)) (Q := (0.629913956902 : ℝ))
      (s := (0.776664925757 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792668237678 : ℝ)) (R := (0.793221387698 : ℝ)) (Q2 := (0.629913956902 : ℝ)) (T := (0.836603674619 : ℝ))
    (B := ((3505288250529217/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263422906323/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3502377141736011/5000000000000000) := by
  have hk1 : kappa q ≤ 0.627112904027 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526845812646 : ℝ)) (s := (0.849960875393 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629101641021 : ℝ) ≤ 0.698528248259 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629101641021 : ℝ)) (Q := (0.629101641021 : ℝ))
      (s := (0.777323050775 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792156616853 : ℝ)) (R := (0.792709766873 : ℝ)) (Q2 := (0.629101641021 : ℝ)) (T := (0.836253684965 : ℝ))
    (B := ((3502377141736011/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (65706247179/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (437433663011037/625000000000000) := by
  have hk1 : kappa q ≤ 0.626302629813 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525649977432 : ℝ)) (s := (0.850700947000 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628289880977 : ℝ) ≤ 0.697944114500 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628289880977 : ℝ)) (Q := (0.628289880977 : ℝ))
      (s := (0.777979322002 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791645016033 : ℝ)) (R := (0.792198166053 : ℝ)) (Q2 := (0.628289880977 : ℝ)) (T := (0.835903959543 : ℝ))
    (B := ((437433663011037/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262227071109/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3496564732108591/5000000000000000) := by
  have hk1 : kappa q ≤ 0.625492910119 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524454142218 : ℝ)) (s := (0.851438695803 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627478676105 : ℝ) ≤ 0.697360665387 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478676105 : ℝ)) (Q := (0.627478676105 : ℝ))
      (s := (0.778633746401 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791133434837 : ℝ)) (R := (0.791686584857 : ℝ)) (Q2 := (0.627478676105 : ℝ)) (T := (0.835554497901 : ℝ))
    (B := ((3496564732108591/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (130814576751/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6987326840682419/10000000000000000) := by
  have hk1 : kappa q ≤ 0.624683744283 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523258307004 : ℝ)) (s := (0.852174127835 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626668025739 : ℝ) ≤ 0.696777899613 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626668025739 : ℝ)) (Q := (0.626668025739 : ℝ))
      (s := (0.779286330893 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790621872883 : ℝ)) (R := (0.791175022903 : ℝ)) (Q2 := (0.626668025739 : ℝ)) (T := (0.835205299589 : ℝ))
    (B := ((6987326840682419/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (52206247179/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3490765363352121/5000000000000000) := by
  have hk1 : kappa q ≤ 0.623875131646 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522062471790 : ℝ)) (s := (0.852907249089 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625857929221 : ℝ) ≤ 0.696195815883 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625857929221 : ℝ)) (Q := (0.625857929221 : ℝ))
      (s := (0.779937082355 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790110329792 : ℝ)) (R := (0.790663479812 : ℝ)) (Q2 := (0.625857929221 : ℝ)) (T := (0.834856364159 : ℝ))
    (B := ((3490765363352121/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16277082393/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6975741111457631/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623067071553 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520866636576 : ℝ)) (s := (0.853638065519 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625048385895 : ℝ) ≤ 0.695614412899 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625048385895 : ℝ)) (Q := (0.625048385895 : ℝ))
      (s := (0.780586007619 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789598805186 : ℝ)) (R := (0.790151955206 : ℝ)) (Q2 := (0.625048385895 : ℝ)) (T := (0.834507691162 : ℝ))
    (B := ((6975741111457631/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259835400681/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6969957984160337/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622259563351 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519670801362 : ℝ)) (s := (0.854366583038 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624239395105 : ℝ) ≤ 0.695033689371 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624239395105 : ℝ)) (Q := (0.624239395105 : ℝ))
      (s := (0.781233113481 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789087298687 : ℝ)) (R := (0.789640448707 : ℝ)) (Q2 := (0.624239395105 : ℝ)) (T := (0.834159280155 : ℝ))
    (B := ((6969957984160337/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129618741537/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1392836266814523/2000000000000000) := by
  have hk1 : kappa q ≤ 0.621452606390 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518474966148 : ℝ)) (s := (0.855092807524 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623430956201 : ℝ) ≤ 0.694453644011 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623430956201 : ℝ)) (Q := (0.623430956201 : ℝ))
      (s := (0.781878406692 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788575809918 : ℝ)) (R := (0.789128959938 : ℝ)) (Q2 := (0.623430956201 : ℝ)) (T := (0.833811130691 : ℝ))
    (B := ((1392836266814523/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258639565467/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6958411150496959/10000000000000000) := by
  have hk1 : kappa q ≤ 0.620646200024 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517279130934 : ℝ)) (s := (0.855816744812 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622623068537 : ℝ) ≤ 0.693874275538 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622623068537 : ℝ)) (Q := (0.622623068537 : ℝ))
      (s := (0.782521893960 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788064338504 : ℝ)) (R := (0.788617488524 : ℝ)) (Q2 := (0.622623068537 : ℝ)) (T := (0.833463242330 : ℝ))
    (B := ((6958411150496959/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12902082393/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952647422777837/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619840343609 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516083295720 : ℝ)) (s := (0.856538400703 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621815731466 : ℝ) ≤ 0.693295582669 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621815731466 : ℝ)) (Q := (0.621815731466 : ℝ))
      (s := (0.783163581956 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787552884070 : ℝ)) (R := (0.788106034090 : ℝ)) (Q2 := (0.621815731466 : ℝ)) (T := (0.833115614627 : ℝ))
    (B := ((6952647422777837/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257443730253/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1389378028060287/2000000000000000) := by
  have hk1 : kappa q ≤ 0.619035036506 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514887460506 : ℝ)) (s := (0.857257780959 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621008944348 : ℝ) ≤ 0.692717564133 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621008944348 : ℝ)) (Q := (0.621008944348 : ℝ))
      (s := (0.783803477308 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787041446243 : ℝ)) (R := (0.787594596263 : ℝ)) (Q2 := (0.621008944348 : ℝ)) (T := (0.832768247145 : ℝ))
    (B := ((1389378028060287/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (128422906323/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1388227858499079/2000000000000000) := by
  have hk1 : kappa q ≤ 0.618230278076 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513691625292 : ℝ)) (s := (0.857974891303 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620202706544 : ℝ) ≤ 0.692140218657 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620202706544 : ℝ)) (Q := (0.620202706544 : ℝ))
      (s := (0.784441586606 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786530024649 : ℝ)) (R := (0.787083174669 : ℝ)) (Q2 := (0.620202706544 : ℝ)) (T := (0.832421139445 : ℝ))
    (B := ((1388227858499079/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (256247895039/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935394868828559/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617426067687 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512495790078 : ℝ)) (s := (0.858689737422 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619397017419 : ℝ) ≤ 0.691563544975 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619397017419 : ℝ)) (Q := (0.619397017419 : ℝ))
      (s := (0.785077916396 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786018618917 : ℝ)) (R := (0.786571768937 : ℝ)) (Q2 := (0.619397017419 : ℝ)) (T := (0.832074291089 : ℝ))
    (B := ((6935394868828559/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (31956247179/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (43310355367567/62500000000000) := by
  have hk1 : kappa q ≤ 0.616622404707 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511299954864 : ℝ)) (s := (0.859402324966 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618591876342 : ℝ) ≤ 0.690987541825 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618591876342 : ℝ)) (Q := (0.618591876342 : ℝ))
      (s := (0.785712473189 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785507228677 : ℝ)) (R := (0.786060378697 : ℝ)) (Q2 := (0.618591876342 : ℝ)) (T := (0.831727701643 : ℝ))
    (B := ((43310355367567/62500000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (10202082393/20000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1384785050398473/2000000000000000) := by
  have hk1 : kappa q ≤ 0.615819288509 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510104119650 : ℝ)) (s := (0.860112659549 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617787282685 : ℝ) ≤ 0.690412207949 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617787282685 : ℝ)) (Q := (0.617787282685 : ℝ))
      (s := (0.786345263452 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784995853560 : ℝ)) (R := (0.785549003580 : ℝ)) (Q2 := (0.617787282685 : ℝ)) (T := (0.831381370674 : ℝ))
    (B := ((1384785050398473/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127227071109/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918200037964429/10000000000000000) := by
  have hk1 : kappa q ≤ 0.615016718467 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508908284436 : ℝ)) (s := (0.860820746749 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616983235820 : ℝ) ≤ 0.689837542092 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616983235820 : ℝ)) (Q := (0.616983235820 : ℝ))
      (s := (0.786976293619 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784484493196 : ℝ)) (R := (0.785037643216 : ℝ)) (Q2 := (0.616983235820 : ℝ)) (T := (0.831035297747 : ℝ))
    (B := ((6918200037964429/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253856224611/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3456240603179023/5000000000000000) := by
  have hk1 : kappa q ≤ 0.614214693962 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507712449222 : ℝ)) (s := (0.861526592106 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616179735125 : ℝ) ≤ 0.689263543005 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616179735125 : ℝ)) (Q := (0.616179735125 : ℝ))
      (s := (0.787605570081 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783973147218 : ℝ)) (R := (0.784526297238 : ℝ)) (Q2 := (0.616179735125 : ℝ)) (T := (0.830689482433 : ℝ))
    (B := ((3456240603179023/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63314576751/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6906768746844307/10000000000000000) := by
  have hk1 : kappa q ≤ 0.613413214373 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506516614008 : ℝ)) (s := (0.862230201127 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615376779982 : ℝ) ≤ 0.688690209443 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615376779982 : ℝ)) (Q := (0.615376779982 : ℝ))
      (s := (0.788233099191 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783461815260 : ℝ)) (R := (0.784014965280 : ℝ)) (Q2 := (0.615376779982 : ℝ)) (T := (0.830343924305 : ℝ))
    (B := ((6906768746844307/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (252660389397/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1725265662283503/2500000000000000) := by
  have hk1 : kappa q ≤ 0.612612279086 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505320778794 : ℝ)) (s := (0.862931579281 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614574369772 : ℝ) ≤ 0.688117540162 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614574369772 : ℝ)) (Q := (0.614574369772 : ℝ))
      (s := (0.788858887267 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782950496956 : ℝ)) (R := (0.783503646976 : ℝ)) (Q2 := (0.614574369772 : ℝ)) (T := (0.829998622931 : ℝ))
    (B := ((1725265662283503/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (25206247179/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895362902977437/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611811887489 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504124943580 : ℝ)) (s := (0.863630732004 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613772503884 : ℝ) ≤ 0.687545533926 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613772503884 : ℝ)) (Q := (0.613772503884 : ℝ))
      (s := (0.789482940586 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782439191942 : ℝ)) (R := (0.782992341962 : ℝ)) (Q2 := (0.613772503884 : ℝ)) (T := (0.829653577888 : ℝ))
    (B := ((6895362902977437/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (251464554183/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3444834749082043/5000000000000000) := by
  have hk1 : kappa q ≤ 0.611012038974 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502929108366 : ℝ)) (s := (0.864327664696 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612971181709 : ℝ) ≤ 0.686974189505 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612971181709 : ℝ)) (Q := (0.612971181709 : ℝ))
      (s := (0.790105265389 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781927899855 : ℝ)) (R := (0.782481049875 : ℝ)) (Q2 := (0.612971181709 : ℝ)) (T := (0.829308788753 : ℝ))
    (B := ((3444834749082043/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (7839582393/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6883982424522463/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610212732933 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501733273152 : ℝ)) (s := (0.865022382724 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612170402637 : ℝ) ≤ 0.686403505666 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612170402637 : ℝ)) (Q := (0.612170402637 : ℝ))
      (s := (0.790725867881 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781416620332 : ℝ)) (R := (0.781969770352 : ℝ)) (Q2 := (0.612170402637 : ℝ)) (T := (0.828964255100 : ℝ))
    (B := ((6883982424522463/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250268718969/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (687830167191983/1000000000000000) := by
  have hk1 : kappa q ≤ 0.609413968766 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500537437938 : ℝ)) (s := (0.865714891418 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611370166067 : ℝ) ≤ 0.685833481188 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611370166067 : ℝ)) (Q := (0.611370166067 : ℝ))
      (s := (0.791344754228 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780905353013 : ℝ)) (R := (0.781458503033 : ℝ)) (Q2 := (0.611370166067 : ℝ)) (T := (0.828619976511 : ℝ))
    (B := ((687830167191983/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499341602723/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3436313615130991/5000000000000000) := by
  have hk1 : kappa q ≤ 0.608615745871 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499341602723 : ℝ)) (s := (0.866405196078 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610570471395 : ℝ) ≤ 0.685264114847 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610570471395 : ℝ)) (Q := (0.610570471395 : ℝ))
      (s := (0.791961930563 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780394097536 : ℝ)) (R := (0.780947247556 : ℝ)) (Q2 := (0.610570471395 : ℝ)) (T := (0.828275952564 : ℝ))
    (B := ((3436313615130991/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498145767509/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (429184943093313/625000000000000) := by
  have hk1 : kappa q ≤ 0.607818063653 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498145767509 : ℝ)) (s := (0.867093301966 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609771318027 : ℝ) ≤ 0.684695405431 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609771318027 : ℝ)) (Q := (0.609771318027 : ℝ))
      (s := (0.792577402979 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779882853543 : ℝ)) (R := (0.780436003563 : ℝ)) (Q2 := (0.609771318027 : ℝ)) (T := (0.827932182844 : ℝ))
    (B := ((429184943093313/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99389986459/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1715324309898767/2500000000000000) := by
  have hk1 : kappa q ≤ 0.607020921520 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496949932295 : ℝ)) (s := (0.867779214313 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608972705370 : ℝ) ≤ 0.684127351728 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608972705370 : ℝ)) (Q := (0.608972705370 : ℝ))
      (s := (0.793191177532 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779371620678 : ℝ)) (R := (0.779924770698 : ℝ)) (Q2 := (0.608972705370 : ℝ)) (T := (0.827588666934 : ℝ))
    (B := ((1715324309898767/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495754097081/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855641670588167/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606224318879 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495754097081 : ℝ)) (s := (0.868462938316 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608174632827 : ℝ) ≤ 0.683559952527 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608174632827 : ℝ)) (Q := (0.608174632827 : ℝ))
      (s := (0.793803260252 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778860398580 : ℝ)) (R := (0.779413548600 : ℝ)) (Q2 := (0.608174632827 : ℝ)) (T := (0.827245404418 : ℝ))
    (B := ((6855641670588167/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (494558261867/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (273999694901197/400000000000000) := by
  have hk1 : kappa q ≤ 0.605428255146 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494558261867 : ℝ)) (s := (0.869144479140 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607377099816 : ℝ) ≤ 0.682993206630 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607377099816 : ℝ)) (Q := (0.607377099816 : ℝ))
      (s := (0.794413657121 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778349186897 : ℝ)) (R := (0.778902336917 : ℝ)) (Q2 := (0.607377099816 : ℝ)) (T := (0.826902394886 : ℝ))
    (B := ((273999694901197/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493362426653/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6844349335515357/10000000000000000) := by
  have hk1 : kappa q ≤ 0.604632729736 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493362426653 : ℝ)) (s := (0.869823841917 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606580105750 : ℝ) ≤ 0.682427112836 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606580105750 : ℝ)) (Q := (0.606580105750 : ℝ))
      (s := (0.795022374093 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777837985273 : ℝ)) (R := (0.778391135293 : ℝ)) (Q2 := (0.606580105750 : ℝ)) (T := (0.826559637926 : ℝ))
    (B := ((6844349335515357/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (492166591439/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3419356274838327/5000000000000000) := by
  have hk1 : kappa q ≤ 0.603837742068 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492166591439 : ℝ)) (s := (0.870501031747 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605783650047 : ℝ) ≤ 0.681861669950 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605783650047 : ℝ)) (Q := (0.605783650047 : ℝ))
      (s := (0.795629417088 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777326793354 : ℝ)) (R := (0.777879943374 : ℝ)) (Q2 := (0.605783650047 : ℝ)) (T := (0.826217133128 : ℝ))
    (B := ((3419356274838327/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19638830249/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (85413525064787/125000000000000) := by
  have hk1 : kappa q ≤ 0.603043291566 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490970756225 : ℝ)) (s := (0.871176053696 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604987732129 : ℝ) ≤ 0.681296876783 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604987732129 : ℝ)) (Q := (0.604987732129 : ℝ))
      (s := (0.796234791989 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776815610788 : ℝ)) (R := (0.777368760808 : ℝ)) (Q2 := (0.604987732129 : ℝ)) (T := (0.825874880086 : ℝ))
    (B := ((85413525064787/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489774921011/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827457692240157/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602249377653 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489774921011 : ℝ)) (s := (0.871848912799 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604192351419 : ℝ) ≤ 0.680732732148 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604192351419 : ℝ)) (Q := (0.604192351419 : ℝ))
      (s := (0.796838504647 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776304437222 : ℝ)) (R := (0.776857587242 : ℝ)) (Q2 := (0.604192351419 : ℝ)) (T := (0.825532878392 : ℝ))
    (B := ((6827457692240157/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488579085797/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (852729950136331/1250000000000000) := by
  have hk1 : kappa q ≤ 0.601455999760 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488579085797 : ℝ)) (s := (0.872519614062 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603397507347 : ℝ) ≤ 0.680169234865 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603397507347 : ℝ)) (Q := (0.603397507347 : ℝ))
      (s := (0.797440560875 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775793272308 : ℝ)) (R := (0.776346422328 : ℝ)) (Q2 := (0.603397507347 : ℝ)) (T := (0.825191127643 : ℝ))
    (B := ((852729950136331/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487383250583/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6816227722013143/10000000000000000) := by
  have hk1 : kappa q ≤ 0.600663157318 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487383250583 : ℝ)) (s := (0.873188162455 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602603199341 : ℝ) ≤ 0.679606383754 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602603199341 : ℝ)) (Q := (0.602603199341 : ℝ))
      (s := (0.798040966458 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775282115694 : ℝ)) (R := (0.775835265714 : ℝ)) (Q2 := (0.602603199341 : ℝ)) (T := (0.824849627436 : ℝ))
    (B := ((6816227722013143/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (486187415369/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1702655511330613/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599870849763 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486187415369 : ℝ)) (s := (0.873854562921 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601809426840 : ℝ) ≤ 0.679044177648 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601809426840 : ℝ)) (Q := (0.601809426840 : ℝ))
      (s := (0.798639727141 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774770967035 : ℝ)) (R := (0.775324117055 : ℝ)) (Q2 := (0.601809426840 : ℝ)) (T := (0.824508377372 : ℝ))
    (B := ((1702655511330613/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96998316031/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1361004512273853/2000000000000000) := by
  have hk1 : kappa q ≤ 0.599079076531 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484991580155 : ℝ)) (s := (0.874518820369 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601016189275 : ℝ) ≤ 0.678482615371 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601016189275 : ℝ)) (Q := (0.601016189275 : ℝ))
      (s := (0.799236848644 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774259825981 : ℝ)) (R := (0.774812976001 : ℝ)) (Q2 := (0.601016189275 : ℝ)) (T := (0.824167377049 : ℝ))
    (B := ((1361004512273853/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483795744941/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799429260539953/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598287837065 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483795744941 : ℝ)) (s := (0.875180939679 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600223486090 : ℝ) ≤ 0.677921695764 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600223486090 : ℝ)) (Q := (0.600223486090 : ℝ))
      (s := (0.799832336647 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773748692188 : ℝ)) (R := (0.774301842208 : ℝ)) (Q2 := (0.600223486090 : ℝ)) (T := (0.823826626072 : ℝ))
    (B := ((6799429260539953/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482599909727/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6793842133256357/10000000000000000) := by
  have hk1 : kappa q ≤ 0.597497130809 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482599909727 : ℝ)) (s := (0.875840925701 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599431316728 : ℝ) ≤ 0.677361417665 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599431316728 : ℝ)) (Q := (0.599431316728 : ℝ))
      (s := (0.800426196802 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773237565310 : ℝ)) (R := (0.773790715330 : ℝ)) (Q2 := (0.599431316728 : ℝ)) (T := (0.823486124045 : ℝ))
    (B := ((6793842133256357/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481404074513/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788261169975581/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596706957209 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481404074513 : ℝ)) (s := (0.876498783253 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598639680634 : ℝ) ≤ 0.676801779919 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598639680634 : ℝ)) (Q := (0.598639680634 : ℝ))
      (s := (0.801018434726 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772726445003 : ℝ)) (R := (0.773279595023 : ℝ)) (Q2 := (0.598639680634 : ℝ)) (T := (0.823145870573 : ℝ))
    (B := ((6788261169975581/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (480208239299/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782685363716077/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595917315718 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480208239299 : ℝ)) (s := (0.877154517124 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597848577258 : ℝ) ≤ 0.676242781373 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597848577258 : ℝ)) (Q := (0.597848577258 : ℝ))
      (s := (0.801609056006 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772215330925 : ℝ)) (R := (0.772768480945 : ℝ)) (Q2 := (0.597848577258 : ℝ)) (T := (0.822805865265 : ℝ))
    (B := ((6782685363716077/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (95802480817/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1355423099406553/2000000000000000) := by
  have hk1 : kappa q ≤ 0.595128205787 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479012404085 : ℝ)) (s := (0.877808132073 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597058006051 : ℝ) ≤ 0.675684420881 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597058006051 : ℝ)) (Q := (0.597058006051 : ℝ))
      (s := (0.802198066198 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771704222733 : ℝ)) (R := (0.772257372753 : ℝ)) (Q2 := (0.597058006051 : ℝ)) (T := (0.822466107730 : ℝ))
    (B := ((1355423099406553/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12525 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477816568871/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6771551768576177/10000000000000000) := by
  have hk1 : kappa q ≤ 0.594339626874 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477816568871 : ℝ)) (s := (0.878459632831 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596267966472 : ℝ) ≤ 0.675126697301 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596267966472 : ℝ)) (Q := (0.596267966472 : ℝ))
      (s := (0.802785470820 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771193120088 : ℝ)) (R := (0.771746270108 : ℝ)) (Q2 := (0.596267966472 : ℝ)) (T := (0.822126597580 : ℝ))
    (B := ((6771551768576177/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part269.S7
namespace BstLean.Part269.S7
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (cs_lower NeededGroup groupTheta groupProfile)
theorem uniform_deviation_upper {n : ℕ} (hn : 12525 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ 0.052853687429 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := BstLean.Part269.S7.wn_upper (by omega : 12525 ≤ n)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.010670920061 :=
    by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hn0).mpr
      nlinarith [cs_lower,hnlo]
  have h2 : √(wn n * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036060725407)
    linarith
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (0.010670920061 + 2 * 0.737676 / 12525) := by gcongr
    _ ≤ (0.052853687429 : ℝ) := by norm_num


theorem uniform_n22_upper {n : ℕ} (hn : 12525 ≤ n) : N22bar n 12 ≤ 0.0015 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar n 12 ≤ 0.000749634 := by
    unfold N12bar
    apply (div_le_iff₀ hn0).mpr
    nlinarith [hnlo]
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem uniform_radial_centre_bound {n : ℕ} (hn : 12525 ≤ n) {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.915146427996 ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnlo : (12525 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := uniform_n22_upper hn
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : (111.915146427996 : ℝ) ≤ √n := le_sqrt_of_sq_le (by linarith [hnlo])
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

theorem uniform_full_formula_bound {n : ℕ} (hn : 12525 ≤ n) {Θ S X T R B : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.003703299838 + 0.003341313488 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003703299838 + 0.003341313488 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.915146427996 ≤ R)
    (hB : (X + 0.052853687429 + R + 0.008540726171) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := uniform_deviation_upper hn hΘ hw.2
  have hr := uniform_radial_centre_bound hn hΘ hT hTsq hR
  have hf : finiteEnergy n n 0.011 ≤ 0.008540726171 := by
    convert (BstLean.Part269.S7.finite_centre_upper (by omega : 12525 ≤ n)) using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

noncomputable def minimumGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => (85943636169/1000000000000)
  | 2 => (86895017887/1000000000000)
  | 3 => (87845846753/1000000000000)
  | 4 => (88797838417/1000000000000)
  | 5 => (11219132199/125000000000)
  | 6 => (90713968531/1000000000000)
  | 7 => (45841744993/500000000000)
  | 8 => (46332527337/500000000000)
  | _ => 0

theorem uniformFullGroup1 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 1) (groupProfile 1) ≤
      0.2654 * groupProfile 1 + 0.003703299838 + 0.003341313488 * groupTheta 1) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 1) (groupProfile 1) 1.22 ≤
      minimumGroupCentre 1 := by
  apply uniform_full_formula_bound hn hm (X := (0.219557470107 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011042897392 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup2 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 2) (groupProfile 2) ≤
      0.2654 * groupProfile 2 + 0.003703299838 + 0.003341313488 * groupTheta 2) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 2) (groupProfile 2) 1.22 ≤
      minimumGroupCentre 2 := by
  apply uniform_full_formula_bound hn hm (X := (0.221125580766 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011158665055 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup3 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 3) (groupProfile 3) ≤
      0.2654 * groupProfile 3 + 0.003703299838 + 0.003341313488 * groupTheta 3) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 3) (groupProfile 3) 1.22 ≤
      minimumGroupCentre 3 := by
  apply uniform_full_formula_bound hn hm (X := (0.222673265699 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011274050347 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup4 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 4) (groupProfile 4) ≤
      0.2654 * groupProfile 4 + 0.003703299838 + 0.003341313488 * groupTheta 4) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 4) (groupProfile 4) 1.22 ≤
      minimumGroupCentre 4 := by
  apply uniform_full_formula_bound hn hm (X := (0.224200730990 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011389061650 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup5 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 5) (groupProfile 5) ≤
      0.2654 * groupProfile 5 + 0.003703299838 + 0.003341313488 * groupTheta 5) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 5) (groupProfile 5) 1.22 ≤
      minimumGroupCentre 5 := by
  apply uniform_full_formula_bound hn hm (X := (0.225708177611 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011503707107 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup6 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 6) (groupProfile 6) ≤
      0.2654 * groupProfile 6 + 0.003703299838 + 0.003341313488 * groupTheta 6) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 6) (groupProfile 6) 1.22 ≤
      minimumGroupCentre 6 := by
  apply uniform_full_formula_bound hn hm (X := (0.227195799930 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011617994507 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup7 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 7) (groupProfile 7) ≤
      0.2654 * groupProfile 7 + 0.003703299838 + 0.003341313488 * groupTheta 7) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 7) (groupProfile 7) 1.22 ≤
      minimumGroupCentre 7 := by
  apply uniform_full_formula_bound hn hm (X := (0.228663787581 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011731931430 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniformFullGroup8 {n : ℕ} (hn : 12525 ≤ n)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta 8) (groupProfile 8) ≤
      0.2654 * groupProfile 8 + 0.003703299838 + 0.003341313488 * groupTheta 8) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta 8) (groupProfile 8) 1.22 ≤
      minimumGroupCentre 8 := by
  apply uniform_full_formula_bound hn hm (X := (0.230112323999 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011845525128 : ℝ))
    <;> norm_num [groupTheta,groupProfile,minimumGroupCentre]

theorem uniform_group_full {n : ℕ} (hn : 12525 ≤ n) {g : Fin 10} (hg : NeededGroup g)
    (hm : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g) :
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

end BstLean.Part269.S7

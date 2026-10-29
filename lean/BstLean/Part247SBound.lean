import BstLean.Part247SSide

namespace BstLean.Part247
open Real Set BstLean.Part130 BstLean.Part182

theorem s_part3U {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ snV c) (hVh : snV c ≤ Vh) (hMh : snM c ≤ Mh)
    (hMl : Ml ≤ snM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 2284 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 1143 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 970 / 100000 + 1144 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 647 / 100000) 0 +
      ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      350 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (647 / 100000 - Ml) 0 + 350 / 100000 ≤ ks) :
    |s3U n 46 eta c| ≤ (n : ℝ) * ks := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩ := s_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := sn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := sn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (647 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  
  have hCpa : s3Cpa n c = n * snV c := by unfold s3Cpa snV; rw [hm]; field_simp
  have hCpp : s3Cpp n c = n * snM c := by unfold s3Cpp snM; rw [hm]; field_simp
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hr1e : s3r1 n 46 = 12 * v + 552 / n := by
    unfold s3r1; rw [hsq2]; field_simp; ring
  have hr1le : s3r1 n 46 ≤ n * (970 / 100000) := by
    rw [hr1e]
    have : 552 / (n : ℝ) ≤ 5 / 100 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hr10 : 0 ≤ s3r1 n 46 := by rw [hr1e]; positivity
  have hrpp : s3rpp n 46 = 8 * v + 368 / n := by
    unfold s3rpp; rw [hsq2]; field_simp; ring
  have hrpp0 : 0 ≤ s3rpp n 46 := by rw [hrpp]; positivity
  have hrpple : s3rpp n 46 ≤ n * (647 / 100000) := by
    rw [hrpp]
    have : 368 / (n : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hnV : n * Vl ≤ n * snV c := mul_le_mul_of_nonneg_left hVl hn0.le
  have hnV' : n * snV c ≤ n * Vh := mul_le_mul_of_nonneg_left hVh hn0.le
  have hCr : 0 ≤ s3Cpa n c - s3r1 n 46 := by
    rw [hCpa]
    have : n * (970 / 100000) ≤ n * Vl := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    linarith
  
  have he0sq : s3e0 n 46 ^ 2 ≤ n * (2 / 10 ^ 6) := by
    rw [he0, div_pow, mul_pow, hvv, h2, hrr]
    have := inv_le (a := 92 * 2) (k := 2 / 10 ^ 6) hnR (by norm_num) (by norm_num)
    linarith
  have hrs := rs_le hn
  have hrs0 : 0 ≤ s3rs n 46 eta := by unfold s3rs; positivity
  have hkd0 : 0 ≤ kdot (s3c1 n 46 c) := kdot_nonneg _
  have hmem1 : s3c1 n 46 c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmem2 : C1 ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, hC1'.le⟩
  have hkd : kdot (s3c1 n 46 c) ≤ kd1 := (kdot_monotoneOn hmem1 hmem2 hc1le).trans hkd1
  set Lh := (Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6 with hLh
  have hLam : s3Lam n 46 c ≤ r * Lh := by
    unfold s3Lam
    have hnum : s3Cpa n c + s3r1 n 46 ≤ n * (Vh + 970 / 100000) := by rw [hCpa]; linarith
    have hnum0 : 0 ≤ s3Cpa n c + s3r1 n 46 := by rw [hCpa]; linarith
    have hden : 0 < r * (1 - 1143 / 10 ^ 6) := by positivity
    have h1 : (s3Cpa n c + s3r1 n 46) / s3am n 46 ≤ n * (Vh + 970 / 100000) / (r * (1 - 1143 / 10 ^ 6)) :=
      div_le_div₀ (by linarith) hnum hden ham
    have h2' : n * (Vh + 970 / 100000) / (r * (1 - 1143 / 10 ^ 6)) =
        r * ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6)) := by
      rw [← hrr]; field_simp
    have e : r * Lh = r * ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6)) + 1142 / 10 ^ 6 * r := by
      rw [hLh]; ring
    linarith
  have hLam0 : 0 ≤ s3Lam n 46 c := by
    unfold s3Lam
    have : 0 ≤ s3Cpa n c + s3r1 n 46 := by rw [hCpa]; linarith
    positivity
  have hC1sq : C1 ^ 2 < 1 := pow_lt_one₀ hC10 hC1' (by norm_num)
  have hcc : s3c1 n 46 c ^ 2 ≤ C1 ^ 2 := pow_le_pow_left₀ hc10 hc1le 2
  have hsqc : 0 < √(1 - s3c1 n 46 c ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hq : 1 / √(1 - s3c1 n 46 c ^ 2) ≤ q1 := by
    refine le_trans ?_ hq1
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by linarith))
    exact Real.sqrt_le_sqrt (by linarith)
  have hq' : 1 ≤ q1 * √(1 - s3c1 n 46 c ^ 2) := by
    rw [div_le_iff₀ hsqc] at hq; linarith
  have hq0 : 0 ≤ q1 := le_trans (by positivity) hq
  have hpi := sn_pi_lo
  have hT2 : s3Lam n 46 c ^ 2 / (π * √(1 - s3c1 n 46 c ^ 2)) ≤
      n * (Lh ^ 2 * q1 / (3141592 / 1000000)) := by
    have hL2 : s3Lam n 46 c ^ 2 ≤ n * Lh ^ 2 := by
      have := pow_le_pow_left₀ hLam0 hLam 2; rw [mul_pow, hrr] at this; exact this
    rw [div_le_iff₀ (by positivity)]
    have hA : s3Lam n 46 c ^ 2 ≤ n * Lh ^ 2 * (q1 * √(1 - s3c1 n 46 c ^ 2)) :=
      hL2.trans (le_mul_of_one_le_right (by positivity) hq')
    have e : n * (Lh ^ 2 * q1 / (3141592 / 1000000)) * (π * √(1 - s3c1 n 46 c ^ 2)) =
        n * Lh ^ 2 * (q1 * √(1 - s3c1 n 46 c ^ 2)) * (π / (3141592 / 1000000)) := by
      field_simp
    rw [e]
    refine hA.trans (le_mul_of_one_le_right (by positivity) ?_)
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hT20 : 0 ≤ s3Lam n 46 c ^ 2 / (π * √(1 - s3c1 n 46 c ^ 2)) := by
    have := Real.pi_pos; positivity
  have hX : s3Cpp n c + s3rpp n 46 ≤ n * (Mh + 647 / 100000) := by
    rw [hCpp]; have := mul_le_mul_of_nonneg_left hMh hn0.le; linarith
  have hXl : n * Ml ≤ s3Cpp n c + s3rpp n 46 := by
    rw [hCpp]; have := mul_le_mul_of_nonneg_left hMl hn0.le; linarith
  have hfirst : (if 0 ≤ s3Cpp n c + s3rpp n 46 then kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46)
      else (s3Cpp n c + s3rpp n 46) / 2) ≤ n * (kd1 * max (Mh + 647 / 100000) 0) := by
    split_ifs with h
    · calc kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46)
          ≤ kd1 * (s3Cpp n c + s3rpp n 46) := mul_le_mul_of_nonneg_right hkd h
        _ ≤ kd1 * (n * max (Mh + 647 / 100000) 0) :=
            mul_le_mul_of_nonneg_left (hX.trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
              hn0.le)) hkdC
        _ = n * (kd1 * max (Mh + 647 / 100000) 0) := by ring
    · have : 0 ≤ n * (kd1 * max (Mh + 647 / 100000) 0) :=
        mul_nonneg hn0.le (mul_nonneg hkdC (le_max_right _ _))
      linarith
  have hfirst' : -(n * ks) ≤ (if 0 ≤ s3Cpp n c + s3rpp n 46 then
      kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46) else (s3Cpp n c + s3rpp n 46) / 2) := by
    split_ifs with h
    · have : 0 ≤ kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46) := mul_nonneg hkd0 h
      have : 0 ≤ n * ks := mul_nonneg hn0.le hks0
      linarith
    · have : n * (-Ml / 2) ≤ n * ks := mul_le_mul_of_nonneg_left hU' hn0.le
      have e : n * (-Ml / 2) = -(n * Ml) / 2 := by ring
      linarith
  have hsum : n * (kd1 * max (Mh + 647 / 100000) 0) + n * (Lh ^ 2 * q1 / (3141592 / 1000000)) +
      n * (2 / 10 ^ 6) + n * (3400 / 10 ^ 6) ≤ n * ks := by
    have := mul_le_mul_of_nonneg_left hU hn0.le
    have e : n * (kd1 * max (Mh + 647 / 100000) 0 + Lh ^ 2 * q1 / (3141592 / 1000000) +
        350 / 100000) = n * (kd1 * max (Mh + 647 / 100000) 0) +
        n * (Lh ^ 2 * q1 / (3141592 / 1000000)) + n * (350 / 100000) := by ring
    have : (n : ℝ) * (2 / 10 ^ 6) + n * (3400 / 10 ^ 6) ≤ n * (350 / 100000) := by
      have e2 : (n : ℝ) * (2 / 10 ^ 6) + n * (3400 / 10 ^ 6) = n * (3402 / 10 ^ 6) := by ring
      rw [e2]; exact mul_le_mul_of_nonneg_left (by norm_num) hn0.le
    linarith
  have hUup : s3U n 46 eta c ≤ n * ks := by unfold s3U; linarith
  have hUlo : -(n * ks) ≤ s3U n 46 eta c := by
    unfold s3U; have := sq_nonneg (s3e0 n 46); linarith
  exact abs_le.2 ⟨hUlo, hUup⟩

theorem s_part3L {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ snV c) (hVh : snV c ≤ Vh) (hMh : snM c ≤ Mh)
    (hMl : Ml ≤ snM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 2284 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 1143 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 970 / 100000 + 1144 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 647 / 100000) 0 +
      ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      350 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (647 / 100000 - Ml) 0 + 350 / 100000 ≤ ks) :
    |s3L n 46 eta c| ≤ (n : ℝ) * ks := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩ := s_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := sn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := sn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (647 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  
  have hCpa : s3Cpa n c = n * snV c := by unfold s3Cpa snV; rw [hm]; field_simp
  have hCpp : s3Cpp n c = n * snM c := by unfold s3Cpp snM; rw [hm]; field_simp
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hr1e : s3r1 n 46 = 12 * v + 552 / n := by
    unfold s3r1; rw [hsq2]; field_simp; ring
  have hr1le : s3r1 n 46 ≤ n * (970 / 100000) := by
    rw [hr1e]
    have : 552 / (n : ℝ) ≤ 5 / 100 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hr10 : 0 ≤ s3r1 n 46 := by rw [hr1e]; positivity
  have hrpp : s3rpp n 46 = 8 * v + 368 / n := by
    unfold s3rpp; rw [hsq2]; field_simp; ring
  have hrpp0 : 0 ≤ s3rpp n 46 := by rw [hrpp]; positivity
  have hrpple : s3rpp n 46 ≤ n * (647 / 100000) := by
    rw [hrpp]
    have : 368 / (n : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hnV : n * Vl ≤ n * snV c := mul_le_mul_of_nonneg_left hVl hn0.le
  have hnV' : n * snV c ≤ n * Vh := mul_le_mul_of_nonneg_left hVh hn0.le
  have hCr : 0 ≤ s3Cpa n c - s3r1 n 46 := by
    rw [hCpa]
    have : n * (970 / 100000) ≤ n * Vl := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    linarith
  
  have he0sq : s3e0 n 46 ^ 2 ≤ n * (2 / 10 ^ 6) := by
    rw [he0, div_pow, mul_pow, hvv, h2, hrr]
    have := inv_le (a := 92 * 2) (k := 2 / 10 ^ 6) hnR (by norm_num) (by norm_num)
    linarith
  have hrs := rs_le hn
  have hrs0 : 0 ≤ s3rs n 46 eta := by unfold s3rs; positivity
  have hkd0 : 0 ≤ kdot (s3c1 n 46 c) := kdot_nonneg _
  have hmem1 : s3c1 n 46 c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmem2 : C1 ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, hC1'.le⟩
  have hkd : kdot (s3c1 n 46 c) ≤ kd1 := (kdot_monotoneOn hmem1 hmem2 hc1le).trans hkd1
  have hmin : -(n * max (647 / 100000 - Ml) 0) ≤ min (s3Cpp n c - s3rpp n 46) 0 := by
    apply le_min
    · have h1 : (n : ℝ) * (647 / 100000 - Ml) ≤ n * max (647 / 100000 - Ml) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hn0.le
      have e : (n : ℝ) * (647 / 100000 - Ml) = n * (647 / 100000) - n * Ml := by ring
      have h3 := mul_le_mul_of_nonneg_left hMl hn0.le
      rw [hCpp]
      linarith
    · have : 0 ≤ n * max (647 / 100000 - Ml) 0 := mul_nonneg hn0.le (le_max_right _ _)
      linarith
  have hm0 : min (s3Cpp n c - s3rpp n 46) 0 ≤ 0 := min_le_right _ _
  have hLprod : kd1 * (-(n * max (647 / 100000 - Ml) 0)) ≤
      kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 := by
    have h1 : kd1 * min (s3Cpp n c - s3rpp n 46) 0 ≤
        kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 :=
      mul_le_mul_of_nonpos_right hkd hm0
    have h2' : kd1 * (-(n * max (647 / 100000 - Ml) 0)) ≤ kd1 * min (s3Cpp n c - s3rpp n 46) 0 :=
      mul_le_mul_of_nonneg_left hmin hkdC
    linarith
  have hLlo : -(n * ks) ≤ s3L n 46 eta c := by
    unfold s3L
    have := mul_le_mul_of_nonneg_left hL hn0.le
    have e : n * (kd1 * max (647 / 100000 - Ml) 0 + 350 / 100000) =
        -(kd1 * (-(n * max (647 / 100000 - Ml) 0))) + n * (350 / 100000) := by ring
    have : (n : ℝ) * (2 / 10 ^ 6) + n * (3400 / 10 ^ 6) ≤ n * (350 / 100000) := by
      have e2 : (n : ℝ) * (2 / 10 ^ 6) + n * (3400 / 10 ^ 6) = n * (3402 / 10 ^ 6) := by ring
      rw [e2]; exact mul_le_mul_of_nonneg_left (by norm_num) hn0.le
    linarith
  have hLup : s3L n 46 eta c ≤ n * ks := by
    unfold s3L
    have : kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hkd0 hm0
    have : 0 ≤ n * ks := mul_nonneg hn0.le hks0
    have := sq_nonneg (s3e0 n 46)
    linarith
  exact abs_le.2 ⟨hLlo, hLup⟩

theorem s_part3 {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ snV c) (hVh : snV c ≤ Vh) (hMh : snM c ≤ Mh)
    (hMl : Ml ≤ snM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 2284 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 1143 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 970 / 100000 + 1144 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 647 / 100000) 0 +
      ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      350 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (647 / 100000 - Ml) 0 + 350 / 100000 ≤ ks) :
    s3nks n 46 eta c ≤ (n : ℝ) * ks := by
  unfold s3nks
  exact max_le (s_part3U hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL) (s_part3L hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL)

theorem s_core {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ snV c) (hVh : snV c ≤ Vh) (hMh : snM c ≤ Mh)
    (hMl : Ml ≤ snM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 2284 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 1143 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 970 / 100000 + 1144 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 647 / 100000) 0 +
      ((Vh + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      350 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (647 / 100000 - Ml) 0 + 350 / 100000 ≤ ks) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 eta c ≤ (n : ℝ) * ks := by
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, -⟩ := s_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  obtain ⟨hCr, hpos⟩ := s_part2 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  exact ⟨ham0, hdm0, hdm2, lt_of_le_of_lt hc1le hC1', hCr, hpos, s_part3 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL⟩



end BstLean.Part247

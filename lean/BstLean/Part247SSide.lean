import BstLean.Part247SBase

namespace BstLean.Part247
open Real Set BstLean.Part130 BstLean.Part182

theorem s_part1 {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
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
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ 0 ≤ s3c1 n 46 c ∧
      s3c1 n 46 c ≤ C1 ∧ √(n : ℝ) * (1 - 1143 / 10 ^ 6) ≤ s3am n 46 ∧
      s3ap n 46 ≤ √(n : ℝ) * (1 + 1142 / 10 ^ 6) ∧ s3e0 n 46 ≤ 1142 / 10 ^ 6 * √(n : ℝ) ∧
      0 ≤ s3e0 n 46 ∧ √(n : ℝ) ≤ s3ap n 46 ∧ 0 ≤ C1 := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
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
  have hvr : v * √2 ≤ 1142 / 10 ^ 6 * (n : ℝ) := by
    have : v * √2 ≤ 95917 / 10000 * (141422 / 100000) := mul_le_mul hv1 h2le h20 (by norm_num)
    linarith
  have he0r : s3e0 n 46 ≤ 1142 / 10 ^ 6 * r := by
    rw [he0, div_le_iff₀ hr0, mul_assoc, hrr']; exact hvr
  have he00 : 0 ≤ s3e0 n 46 := by rw [he0]; positivity
  
  have hap : s3ap n 46 = r + s3e0 n 46 := by unfold s3ap s3e0; ring
  have hap1 : s3ap n 46 ≤ r * (1 + 1142 / 10 ^ 6) := by rw [hap]; linarith
  have hap0 : r ≤ s3ap n 46 := by rw [hap]; linarith
  have hsq : r * (1 - 1 / 10 ^ 8) ≤ √((n : ℝ) - 2 / n) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hrr]
    have h1 : 2 / (n : ℝ) ≤ (2 / 10 ^ 8 - 1 / 10 ^ 16) * n :=
      inv_le hnR (by norm_num) (by norm_num)
    have e : (n : ℝ) * (1 - 1 / 10 ^ 8) ^ 2 = n - (2 / 10 ^ 8 - 1 / 10 ^ 16) * n := by ring
    linarith
  have ham : r * (1 - 1143 / 10 ^ 6) ≤ s3am n 46 := by
    unfold s3am; rw [he0']; linarith
  have ham0 : 0 < s3am n 46 := lt_of_lt_of_le (by positivity) ham
  
  have hX0 : (r * (dlo + 2284 / 10 ^ 6)) ^ 2 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) := by
    rw [mul_pow, hrr]
    have h8 : 8 / (n : ℝ) ≤ (1 / 10 ^ 7) * n := inv_le hnR (by norm_num) (by norm_num)
    have h1 : (n : ℝ) * (dlo + 2284 / 10 ^ 6) ^ 2 ≤ n * (2 * (1 - κh) - 1 / 10 ^ 7) :=
      mul_le_mul_of_nonneg_left hd hn0.le
    have h2' : (n : ℝ) * (2 * (1 - κh)) ≤ 2 * n * (1 - kappa c) := by
      have := mul_le_mul_of_nonneg_left hκ (by positivity : (0 : ℝ) ≤ 2 * n)
      have e3 : (n : ℝ) * (2 * (1 - κh)) = 2 * n - 2 * n * κh := by ring
      have e4 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * n * kappa c := by ring
      linarith
    have e : 4 * (2 / (n : ℝ)) = 8 / n := by ring
    have e1 : (n : ℝ) * (2 * (1 - κh) - 1 / 10 ^ 7) = n * (2 * (1 - κh)) - (1 / 10 ^ 7) * n := by ring
    rw [e]; linarith
  have hdm : r * dlo ≤ s3dm n 46 c := by
    unfold s3dm
    have hs := Real.le_sqrt_of_sq_le hX0
    rw [he0']
    have : 2 * s3e0 n 46 ≤ r * (2284 / 10 ^ 6) := by linarith
    have e : r * (dlo + 2284 / 10 ^ 6) = r * dlo + r * (2284 / 10 ^ 6) := by ring
    linarith
  have hdm0 : 0 ≤ s3dm n 46 c := le_trans (by positivity) hdm
  
  have hXnn : 0 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) := le_trans (sq_nonneg _) hX0
  have hdm2 : s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 := by
    have hle : s3dm n 46 c ≤ √(2 * n * (1 - kappa c) - 4 * (2 / n)) := by
      unfold s3dm; rw [he0']; linarith
    have h1 : s3dm n 46 c ^ 2 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) :=
      (pow_le_pow_left₀ hdm0 hle 2).trans (le_of_eq (Real.sq_sqrt hXnn))
    have h2' : 2 * (n : ℝ) * (1 - kappa c) - 4 * (2 / n) ≤ 2 * r ^ 2 := by
      rw [hrr]
      have : 0 ≤ 4 * (2 / (n : ℝ)) := by positivity
      have : 2 * (n : ℝ) * (1 - kappa c) ≤ 2 * n := by
        have h5 := mul_le_mul_of_nonneg_left hκ0 (by positivity : (0 : ℝ) ≤ 2 * n)
        have e4 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * n * kappa c := by ring
        rw [mul_zero] at h5; linarith
      linarith
    have h3 : r ^ 2 ≤ s3ap n 46 ^ 2 := pow_le_pow_left₀ hr0.le hap0 2
    linarith
  
  have hdlo2 : dlo ^ 2 ≤ 2 := by
    have h1 : dlo ^ 2 ≤ (dlo + 2284 / 10 ^ 6) ^ 2 := pow_le_pow_left₀ hdlo (by linarith) 2
    have : 0 ≤ κh := le_trans hκ0 hκ
    linarith
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) := by
      have : (2 : ℝ) ≤ 2 * (1 + 1142 / 10 ^ 6) ^ 2 := by norm_num
      linarith
    have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 2 * (1 - 1143 / 10 ^ 6) ^ 2)
    linarith
  have hc1le : s3c1 n 46 c ≤ C1 := by
    unfold s3c1
    have hden : 0 < 2 * s3am n 46 ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hCnum : 2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2 ≤ C1 * (2 * (1 - 1143 / 10 ^ 6) ^ 2) := by
      rwa [div_le_iff₀ (by norm_num)] at hC1
    have ha2 : s3ap n 46 ^ 2 ≤ (r * (1 + 1142 / 10 ^ 6)) ^ 2 := pow_le_pow_left₀ (by linarith) hap1 2
    have hd2 : (r * dlo) ^ 2 ≤ s3dm n 46 c ^ 2 := pow_le_pow_left₀ (by positivity) hdm 2
    have hm2 : (r * (1 - 1143 / 10 ^ 6)) ^ 2 ≤ s3am n 46 ^ 2 :=
      pow_le_pow_left₀ (by positivity) ham 2
    have h4 : r ^ 2 * (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) ≤
        r ^ 2 * (C1 * (2 * (1 - 1143 / 10 ^ 6) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCnum (by positivity)
    have h5 : C1 * (2 * (r * (1 - 1143 / 10 ^ 6)) ^ 2) ≤ C1 * (2 * s3am n 46 ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC10
    have e1 : (r * (1 + 1142 / 10 ^ 6)) ^ 2 = r ^ 2 * (1 + 1142 / 10 ^ 6) ^ 2 := by ring
    have e2 : (r * dlo) ^ 2 = r ^ 2 * dlo ^ 2 := by ring
    have e3 : C1 * (2 * (r * (1 - 1143 / 10 ^ 6)) ^ 2) =
        r ^ 2 * (C1 * (2 * (1 - 1143 / 10 ^ 6) ^ 2)) := by ring
    have e4 : r ^ 2 * (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) =
        2 * (r ^ 2 * (1 + 1142 / 10 ^ 6) ^ 2) - r ^ 2 * dlo ^ 2 := by ring
    linarith
  have hc10 : 0 ≤ s3c1 n 46 c := by
    unfold s3c1; exact div_nonneg (by linarith) (by positivity)
  exact ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩

theorem s_part2 {n : ℕ} (hn : 11883 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
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
    0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 := by
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
  refine ⟨hCr, ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    have h1 : s3e0 n 46 * s3ap n 46 ≤ 1142 / 10 ^ 6 * r * (r * (1 + 1142 / 10 ^ 6)) :=
      mul_le_mul he0r hap1 (by linarith) (by positivity)
    have e : 1142 / 10 ^ 6 * r * (r * (1 + 1142 / 10 ^ 6)) = n * (1142 / 10 ^ 6 * (1 + 1142 / 10 ^ 6)) := by
      rw [← hrr]; ring
    have h2' : n * (1142 / 10 ^ 6 * (1 + 1142 / 10 ^ 6)) ≤ n * (Vl - 970 / 100000) :=
      mul_le_mul_of_nonneg_left (by norm_num; linarith) hn0.le
    rw [hCpa]
    have e2 : n * (Vl - 970 / 100000) = n * Vl - n * (970 / 100000) := by ring
    linarith


end BstLean.Part247

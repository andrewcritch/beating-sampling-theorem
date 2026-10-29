import BstLean.Part247SBound

/-! Part 247: overlap-cell certificates for the S block and side conditions. -/
namespace BstLean.Part247
open Real Set BstLean.Part130 BstLean.Part182

theorem s_cell {n : ℕ} (hn : 11883 ≤ n) {c cl ch Su Sd Sc dlo C1 q1 kd1 ks : ℝ}
    (hcl0 : 0 ≤ cl) (hcl : cl ≤ c) (hch : c ≤ ch) (hch1 : ch ≤ 3 / 4)
    (hSu0 : 0 ≤ Su) (hSu : 1 - cl ^ 2 ≤ Su ^ 2) (hSd0 : 0 ≤ Sd) (hSd : Sd ^ 2 ≤ 1 - ch ^ 2)
    (hSc0 : 0 ≤ Sc) (hSc : 1 - ch ^ 2 ≤ Sc ^ 2)
    (hdlo : 0 ≤ dlo)
    (hd : (dlo + 2284 / 10 ^ 6) ^ 2 ≤
      2 * (1 - (Sc + ch * (3141593 / 2000000 + snP7 ch)) / (3141592 / 1000000)) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 1142 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 1143 / 10 ^ 6) ^ 2) ≤ C1)
    (hC10 : 0 ≤ C1) (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq10 : 0 ≤ q1) (hq1 : 1 ≤ q1 ^ 2 * (1 - C1 ^ 2))
    (hVl' : 970 / 100000 + 1144 / 10 ^ 6 ≤ Sd * snKL cl)
    (hU : kd1 * max (Su / (3141592 / 1000000) - cl * snKL cl + 647 / 100000) 0 +
      ((Su * snKU ch + 970 / 100000) / (1 - 1143 / 10 ^ 6) + 1142 / 10 ^ 6) ^ 2 * q1 /
        (3141592 / 1000000) + 350 / 100000 ≤ ks)
    (hU' : -(Sd / (3141593 / 1000000) - ch * snKU ch) / 2 ≤ ks)
    (hL : kd1 * max (647 / 100000 - (Sd / (3141593 / 1000000) - ch * snKU ch)) 0 +
      350 / 100000 ≤ ks) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 eta c ≤ (n : ℝ) * ks ∧
      s3c1 n 46 c ≤ C1 := by
  have hc0 : 0 ≤ c := hcl0.trans hcl
  have hc1 : c ≤ 3 / 4 := hch.trans hch1
  have hcl1 : cl ≤ 3 / 4 := hcl.trans hc1
  have hch0 : 0 ≤ ch := hc0.trans hch
  have hpl := sn_pi_lo
  have hph := sn_pi_hi
  have hpi := Real.pi_pos
  
  have hsc : √(1 - c ^ 2) ≤ Su := by
    refine (Real.sqrt_le_sqrt (by nlinarith)).trans (sn_sqrt_le hSu0 hSu)
  have hsc' : Sd ≤ √(1 - c ^ 2) := by
    refine (sn_sqrt_ge hSd0 hSd).trans (Real.sqrt_le_sqrt (by nlinarith))
  have hsch : √(1 - ch ^ 2) ≤ Sc := sn_sqrt_le hSc0 hSc
  have hs0 : 0 ≤ √(1 - c ^ 2) := Real.sqrt_nonneg _
  
  have hmc : c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmch : ch ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmcl : cl ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hk1 : kdot c ≤ snKU ch := (kdot_monotoneOn hmc hmch hch).trans (sn_kU hch0 hch1)
  have hk2 : snKL cl ≤ kdot c := (sn_kL hcl0 hcl1).trans (kdot_monotoneOn hmcl hmc hcl)
  have hkl0 : 0 ≤ snKL cl := by unfold snKL snP5; positivity
  have hkc0 : 0 ≤ kdot c := kdot_nonneg c
  
  have hκ : kappa c ≤ (Sc + ch * (3141593 / 2000000 + snP7 ch)) / (3141592 / 1000000) :=
    (kappa_monotoneOn hmc hmch hch).trans (sn_kappa_le hch0 hch1 hsch)
  
  have hVh : snV c ≤ Su * snKU ch := mul_le_mul hsc hk1 hkc0 hSu0
  have hVl : Sd * snKL cl ≤ snV c := mul_le_mul hsc' hk2 hkl0 hs0
  have hMh : snM c ≤ Su / (3141592 / 1000000) - cl * snKL cl := by
    unfold snM
    have h1 : √(1 - c ^ 2) / π ≤ Su / (3141592 / 1000000) :=
      (div_le_div_of_nonneg_left hs0 (by norm_num) hpl.le).trans
        (div_le_div_of_nonneg_right hsc (by norm_num))
    have h2 : cl * snKL cl ≤ c * kdot c := mul_le_mul hcl hk2 hkl0 hc0
    linarith
  have hMl : Sd / (3141593 / 1000000) - ch * snKU ch ≤ snM c := by
    unfold snM
    have h1 : Sd / (3141593 / 1000000) ≤ √(1 - c ^ 2) / π :=
      (div_le_div_of_nonneg_right hsc' (by norm_num)).trans
        (div_le_div_of_nonneg_left hs0 hpi hph.le)
    have h2 : c * kdot c ≤ ch * snKU ch := mul_le_mul hch hk1 hkc0 hch0
    linarith
  
  have hq : 1 / √(1 - C1 ^ 2) ≤ q1 := by
    have hpos : 0 < 1 - C1 ^ 2 := by nlinarith
    have hs : 0 < √(1 - C1 ^ 2) := Real.sqrt_pos.2 hpos
    rw [div_le_iff₀ hs]
    have : 1 ≤ √(q1 ^ 2 * (1 - C1 ^ 2)) := by
      have := Real.sqrt_le_sqrt hq1
      rwa [Real.sqrt_one] at this
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq10] at this
  have hs := s_core hn hc0 (by linarith) hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq
    (hVl'.trans le_rfl) hU hU' hL


  have ht := s_part1 hn hc0 (by linarith) hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq
    hVl' hU hU' hL
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2, ht.2.2.2.2.1⟩

end BstLean.Part247

import BstLean.Part253All

namespace BstLean.Part281.HS12224
open Real Set BstLean.Part194 BstLean.Part211 BstLean.Part253

theorem S0_lower_12224 : (11457 : ℝ) ≤ S0 12224 := by
  have hs : √(12 * (12224 - 1 : ℝ)) ≤ 383 := sqrt_le_iff.mpr (by norm_num)
  unfold S0
  simp only [Nat.cast_ofNat]
  linarith

theorem a0_upper_12224 : a0 12224 ≤ 0.00595952 := by
  have hs24 : √(24 : ℝ) ≤ 4.89897949 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hn : (110.562199 : ℝ) ≤ √12224 := le_sqrt_of_sq_le (by norm_num)
  have hn2 : (10.51485 : ℝ) ≤ √(√12224) := le_sqrt_of_sq_le (by linarith)
  unfold a0
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (4.89897949 : ℝ) / (1.414213562 * 110.562199 * 10.51485) := by gcongr
    _ ≤ (0.00595952 : ℝ) := by norm_num

theorem hs_interval_12224 {θ a b C D Q K A T S : ℝ}
    (hw : θ ∈ Icc a b) (ha : 0 < a) (hb : b ≤ 1)
    (hC : 2 * (1 - a) / (3.141592 * a) ≤ C) (hC0 : 0 ≤ C)
    (hD : 1 + 2 * C * 12224 / 11457 ≤ D ^ 2) (hD0 : 0 < D)
    (hQ : 1 - ((1 - 0.00000615) * (1 - 1 / 11457)) / D / 2 ≤ Q)
    (hCH : (1 + 0.006) * (Q ^ 2 + 1 / 12224) +
      (1 + 1 / 0.006) * (3 / (16 * 12224)) + 4 * (1 + 2 / 12224) / 12224 ≤ K ^ 4)
    (hK : 0 ≤ K) (hA : 0 < A) (hAsq : A ^ 2 ≤ a)
    (hT : 0 ≤ T) (hTsq : b ≤ T ^ 2)
    (hS : (K + 0.00595952 / A) ^ 4 * (b * T) ≤ S) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ S := by
  have hθ := ha.trans_le hw.1
  have hθ1 := hw.2.trans hb
  have hlo := hw.1
  have hhi := hw.2
  have hb0 : 0 ≤ b := hθ.le.trans hhi
  have hj := J0_bounds (by norm_num : 64 ≤ 12224) hθ hθ1
  have hc : axialC θ ≤ C := by
    unfold axialC
    apply le_trans ?_ hC
    apply div_le_div₀ (by have := hw.1; have := hw.2; nlinarith : 0 ≤ 2 * (1 - a))
      (by have := hw.1; linarith) (mul_pos (by norm_num) ha)
    have hp := pi_gt_d6.le
    gcongr
  have hs0 := S0_lower_12224
  have hd : √(1 + 2 * axialC θ * 12224 / S0 12224) ≤ D := by
    apply sqrt_le_iff.mpr
    refine ⟨hD0.le, ?_⟩
    apply le_trans ?_ hD
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    gcongr
  have hden : 0 < √(1 + 2 * axialC θ * 12224 / S0 12224) := by
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    have hspos : 0 < S0 12224 := by linarith
    positivity
  have hn : (1 - 0.00000615 : ℝ) * (1 - 1 / 11457) ≤
      (1 - exp (-12)) * (1 - 1 / S0 12224) := by
    have he := exp_minus_twelve_upper
    have he0 : 0 ≤ 1 - exp (-12 : ℝ) := by linarith
    have hs : (1 : ℝ) / S0 12224 ≤ 1 / 11457 := by
      gcongr
    gcongr
  have hJ : ((1 - 0.00000615 : ℝ) * (1 - 1 / 11457)) / D ≤ J0 12224 θ := by
    unfold J0
    simp only [Nat.cast_ofNat]
    exact div_le_div₀ (le_trans (by norm_num) hn) hn hden hd
  have hq : qHS 12224 θ ≤ Q := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS 12224 θ := by linarith [hj.2.2.1]
  have hqQ : 0 ≤ Q := hq0.trans hq
  have hch : CH 12224 θ 0.006 ≤ K ^ 4 := by
    unfold CH
    simp only [Nat.cast_ofNat]
    apply le_trans ?_ hCH
    gcongr
  have hroot : √(√(CH 12224 θ 0.006)) ≤ K := by
    apply sqrt_le_iff.mpr
    refine ⟨hK, sqrt_le_iff.mpr ⟨sq_nonneg K, ?_⟩⟩
    simpa only [← pow_mul] using hch
  have hθroot : A ≤ √θ := le_sqrt_of_sq_le (hAsq.trans hw.1)
  have hθroot1 : √θ ≤ T := sqrt_le_iff.mpr ⟨hT, hw.2.trans hTsq⟩
  rw [hsProfile_eq_paper (by norm_num) hθ]
  have ha0 : 0 ≤ a0 12224 := by unfold a0; positivity
  have ha0u := a0_upper_12224
  apply le_trans ?_ hS
  gcongr


theorem hsGroup1Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4617991745) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.679558072942 : ℝ))
    <;> norm_num

theorem hsGroup1Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4617991745 : ℝ) 0.463598349) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.741944501462 : ℝ)) (D := (1.607242792614 : ℝ))
    (Q := (0.688937299254 : ℝ)) (K := (0.832559271109 : ℝ))
    (A := (0.679558072941 : ℝ)) (T := (0.680880568823 : ℝ))
    <;> norm_num

theorem hsGroup1Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.463598349 : ℝ) 0.4653975235) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.736594443742 : ℝ)) (D := (1.603687297868 : ℝ))
    (Q := (0.688247649969 : ℝ)) (K := (0.832145045266 : ℝ))
    (A := (0.680880568822 : ℝ)) (T := (0.682200500953 : ℝ))
    <;> norm_num

theorem hsGroup1Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4653975235 : ℝ) 0.467196698) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.731285751464 : ℝ)) (D := (1.600151484597 : ℝ))
    (Q := (0.687558778879 : ℝ)) (K := (0.831731083463 : ℝ))
    (A := (0.682200500952 : ℝ)) (T := (0.683517884185 : ℝ))
    <;> norm_num

theorem hsGroup1Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.467196698 : ℝ) 0.4689958725) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.726017946735 : ℝ)) (D := (1.596635164208 : ℝ))
    (Q := (0.686870679644 : ℝ)) (K := (0.831317382281 : ℝ))
    (A := (0.683517884184 : ℝ)) (T := (0.684832733228 : ℝ))
    <;> norm_num

theorem hsGroup1Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4689958725 : ℝ) 0.470795047) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.720790558992 : ℝ)) (D := (1.593138150631 : ℝ))
    (Q := (0.686183345978 : ℝ)) (K := (0.830903938326 : ℝ))
    (A := (0.684832733227 : ℝ)) (T := (0.686145062651 : ℝ))
    <;> norm_num

theorem hsGroup1Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.470795047 : ℝ) 0.4725942215) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.715603124868 : ℝ)) (D := (1.589660260278 : ℝ))
    (Q := (0.685496771657 : ℝ)) (K := (0.830490748235 : ℝ))
    (A := (0.686145062650 : ℝ)) (T := (0.687454886884 : ℝ))
    <;> norm_num

theorem hsGroup1Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4725942215 : ℝ) 0.474393396) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  apply hs_interval_12224 hw (C := (0.710455188049 : ℝ)) (D := (1.586201312004 : ℝ))
    (Q := (0.684810950513 : ℝ)) (K := (0.830077808672 : ℝ))
    (A := (0.687454886883 : ℝ)) (T := (0.688762220219 : ℝ))
    <;> norm_num

theorem hsGroup1_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.474393396) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.161707958858 := by
  by_cases h0 : θ ≤ 0.4617991745
  · apply hsGroup1Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.463598349
  · apply hsGroup1Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4653975235
  · apply hsGroup1Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.467196698
  · apply hsGroup1Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4689958725
  · apply hsGroup1Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.470795047
  · apply hsGroup1Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.4725942215
  · apply hsGroup1Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup1Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup2Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.462698761625) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680219642193 : ℝ))
    <;> norm_num

theorem hsGroup2Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.462698761625 : ℝ) 0.46539752325) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.739264272134 : ℝ)) (D := (1.605462573416 : ℝ))
    (Q := (0.688592376986 : ℝ)) (K := (0.832352124996 : ℝ))
    (A := (0.680219642192 : ℝ)) (T := (0.682200500770 : ℝ))
    <;> norm_num

theorem hsGroup2Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.46539752325 : ℝ) 0.468096284875) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.731285752199 : ℝ)) (D := (1.600151485087 : ℝ))
    (Q := (0.687558778975 : ℝ)) (K := (0.831731083520 : ℝ))
    (A := (0.682200500769 : ℝ)) (T := (0.684175624292 : ℝ))
    <;> norm_num

theorem hsGroup2Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.468096284875 : ℝ) 0.4707950465) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.723399230957 : ℝ)) (D := (1.594884256328 : ℝ))
    (Q := (0.686526917648 : ℝ)) (K := (0.831110628447 : ℝ))
    (A := (0.684175624291 : ℝ)) (T := (0.686145062287 : ℝ))
    <;> norm_num

theorem hsGroup2Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4707950465 : ℝ) 0.473493808125) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.715603126304 : ℝ)) (D := (1.589660261242 : ℝ))
    (Q := (0.685496771848 : ℝ)) (K := (0.830490748350 : ℝ))
    (A := (0.686145062286 : ℝ)) (T := (0.688108863572 : ℝ))
    <;> norm_num

theorem hsGroup2Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.473493808125 : ℝ) 0.47619256975) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.707895892202 : ℝ)) (D := (1.584478886389 : ℝ))
    (Q := (0.684468320708 : ℝ)) (K := (0.829871431946 : ℝ))
    (A := (0.688108863571 : ℝ)) (T := (0.690067076269 : ℝ))
    <;> norm_num

theorem hsGroup2Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.47619256975 : ℝ) 0.478891331375) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.700276017665 : ℝ)) (D := (1.579339530477 : ℝ))
    (Q := (0.683441543647 : ℝ)) (K := (0.829252668086 : ℝ))
    (A := (0.690067076268 : ℝ)) (T := (0.692019747822 : ℝ))
    <;> norm_num

theorem hsGroup2Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.478891331375 : ℝ) 0.481590093) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  apply hs_interval_12224 hw (C := (0.692742025764 : ℝ)) (D := (1.574241604044 : ℝ))
    (Q := (0.682416420363 : ℝ)) (K := (0.828634445760 : ℝ))
    (A := (0.692019747821 : ℝ)) (T := (0.693966925005 : ℝ))
    <;> norm_num

theorem hsGroup2_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.481590093) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.164221155935 := by
  by_cases h0 : θ ≤ 0.462698761625
  · apply hsGroup2Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46539752325
  · apply hsGroup2Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.468096284875
  · apply hsGroup2Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4707950465
  · apply hsGroup2Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.473493808125
  · apply hsGroup2Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.47619256975
  · apply hsGroup2Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.478891331375
  · apply hsGroup2Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup2Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup3Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.463598348875) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680880568731 : ℝ))
    <;> norm_num

theorem hsGroup3Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.463598348875 : ℝ) 0.46719669775) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.736594444112 : ℝ)) (D := (1.603687298114 : ℝ))
    (Q := (0.688247650017 : ℝ)) (K := (0.832145045295 : ℝ))
    (A := (0.680880568730 : ℝ)) (T := (0.683517884002 : ℝ))
    <;> norm_num

theorem hsGroup3Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.46719669775 : ℝ) 0.470795046625) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.726017947464 : ℝ)) (D := (1.596635164695 : ℝ))
    (Q := (0.686870679739 : ℝ)) (K := (0.831317382338 : ℝ))
    (A := (0.683517884001 : ℝ)) (T := (0.686145062378 : ℝ))
    <;> norm_num

theorem hsGroup3Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.470795046625 : ℝ) 0.4743933955) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.715603125945 : ℝ)) (D := (1.589660261001 : ℝ))
    (Q := (0.685496771800 : ℝ)) (K := (0.830490748321 : ℝ))
    (A := (0.686145062377 : ℝ)) (T := (0.688762219856 : ℝ))
    <;> norm_num

theorem hsGroup3Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4743933955 : ℝ) 0.477991744375) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.705346300560 : ℝ)) (D := (1.582761128013 : ℝ))
    (Q := (0.684125876623 : ℝ)) (K := (0.829665116440 : ℝ))
    (A := (0.688762219855 : ℝ)) (T := (0.691369470237 : ℝ))
    <;> norm_num

theorem hsGroup3Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.477991744375 : ℝ) 0.48159009325) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.695243903097 : ℝ)) (D := (1.575936345094 : ℝ))
    (Q := (0.682757945534 : ℝ)) (K := (0.828840460325 : ℝ))
    (A := (0.691369470236 : ℝ)) (T := (0.693966925185 : ℝ))
    <;> norm_num

theorem hsGroup3Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.48159009325 : ℝ) 0.485188442125) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.685292471990 : ℝ)) (D := (1.569184528703 : ℝ))
    (Q := (0.681392930735 : ℝ)) (K := (0.828016754028 : ℝ))
    (A := (0.693966925184 : ℝ)) (T := (0.696554694282 : ℝ))
    <;> norm_num

theorem hsGroup3Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.485188442125 : ℝ) 0.488786791) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  apply hs_interval_12224 hw (C := (0.675488648360 : ℝ)) (D := (1.562504331149 : ℝ))
    (Q := (0.680030785286 : ℝ)) (K := (0.827193972016 : ℝ))
    (A := (0.696554694281 : ℝ)) (T := (0.699132885080 : ℝ))
    <;> norm_num

theorem hsGroup3_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.488786791) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.166718606529 := by
  by_cases h0 : θ ≤ 0.463598348875
  · apply hsGroup3Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46719669775
  · apply hsGroup3Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.470795046625
  · apply hsGroup3Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4743933955
  · apply hsGroup3Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.477991744375
  · apply hsGroup3Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.48159009325
  · apply hsGroup3Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.485188442125
  · apply hsGroup3Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup3Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup4Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.464497936125) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.681540854334 : ℝ))
    <;> norm_num

theorem hsGroup4Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.464497936125 : ℝ) 0.46899587225) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.733934957333 : ℝ)) (D := (1.601916943140 : ℝ))
    (Q := (0.687903117595 : ℝ)) (K := (0.831938031602 : ℝ))
    (A := (0.681540854333 : ℝ)) (T := (0.684832733046 : ℝ))
    <;> norm_num

theorem hsGroup4Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.46899587225 : ℝ) 0.473493808375) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.720790559716 : ℝ)) (D := (1.593138151115 : ℝ))
    (Q := (0.686183346073 : ℝ)) (K := (0.830903938383 : ℝ))
    (A := (0.684832733045 : ℝ)) (T := (0.688108863753 : ℝ))
    <;> norm_num

theorem hsGroup4Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.473493808375 : ℝ) 0.4779917445) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.707895891492 : ℝ)) (D := (1.584478885911 : ℝ))
    (Q := (0.684468320612 : ℝ)) (K := (0.829871431888 : ℝ))
    (A := (0.688108863752 : ℝ)) (T := (0.691369470327 : ℝ))
    <;> norm_num

theorem hsGroup4Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4779917445 : ℝ) 0.482489680625) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.695243902749 : ℝ)) (D := (1.575936344859 : ℝ))
    (Q := (0.682757945486 : ℝ)) (K := (0.828840460296 : ℝ))
    (A := (0.691369470326 : ℝ)) (T := (0.694614771385 : ℝ))
    <;> norm_num

theorem hsGroup4Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.482489680625 : ℝ) 0.48698761675) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.682827806459 : ℝ)) (D := (1.567507816631 : ℝ))
    (Q := (0.681052127127 : ℝ)) (K := (0.827810972826 : ℝ))
    (A := (0.694614771384 : ℝ)) (T := (0.697844980458 : ℝ))
    <;> norm_num

theorem hsGroup4Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.48698761675 : ℝ) 0.491485552875) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.670641066342 : ℝ)) (D := (1.559190677449 : ℝ))
    (Q := (0.679350774054 : ℝ)) (K := (0.826782919702 : ℝ))
    (A := (0.697844980457 : ℝ)) (T := (0.701060306162 : ℝ))
    <;> norm_num

theorem hsGroup4Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.491485552875 : ℝ) 0.495983489) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  apply hs_interval_12224 hw (C := (0.658677385390 : ℝ)) (D := (1.550982387470 : ℝ))
    (Q := (0.677653796803 : ℝ)) (K := (0.825756252115 : ℝ))
    (A := (0.701060306161 : ℝ)) (T := (0.704260952347 : ℝ))
    <;> norm_num

theorem hsGroup4_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.495983489) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.169199944501 := by
  by_cases h0 : θ ≤ 0.464497936125
  · apply hsGroup4Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46899587225
  · apply hsGroup4Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.473493808375
  · apply hsGroup4Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4779917445
  · apply hsGroup4Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.482489680625
  · apply hsGroup4Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.48698761675
  · apply hsGroup4Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.491485552875
  · apply hsGroup4Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup4Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup5Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46539752325) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682200500770 : ℝ))
    <;> norm_num

theorem hsGroup5Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.46539752325 : ℝ) 0.4707950465) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.731285752199 : ℝ)) (D := (1.600151485087 : ℝ))
    (Q := (0.687558778975 : ℝ)) (K := (0.831731083520 : ℝ))
    (A := (0.682200500769 : ℝ)) (T := (0.686145062287 : ℝ))
    <;> norm_num

theorem hsGroup5Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4707950465 : ℝ) 0.47619256975) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.715603126304 : ℝ)) (D := (1.589660261242 : ℝ))
    (Q := (0.685496771848 : ℝ)) (K := (0.830490748350 : ℝ))
    (A := (0.686145062286 : ℝ)) (T := (0.690067076269 : ℝ))
    <;> norm_num

theorem hsGroup5Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.47619256975 : ℝ) 0.481590093) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.700276017665 : ℝ)) (D := (1.579339530477 : ℝ))
    (Q := (0.683441543647 : ℝ)) (K := (0.829252668086 : ℝ))
    (A := (0.690067076268 : ℝ)) (T := (0.693966925005 : ℝ))
    <;> norm_num

theorem hsGroup5Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.481590093 : ℝ) 0.48698761625) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.685292472677 : ℝ)) (D := (1.569184529170 : ℝ))
    (Q := (0.681392930830 : ℝ)) (K := (0.828016754086 : ℝ))
    (A := (0.693966925004 : ℝ)) (T := (0.697844980100 : ℝ))
    <;> norm_num

theorem hsGroup5Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.48698761625 : ℝ) 0.4923851395) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.670641067684 : ℝ)) (D := (1.559190678367 : ℝ))
    (Q := (0.679350774243 : ℝ)) (K := (0.826782919816 : ℝ))
    (A := (0.697844980099 : ℝ)) (T := (0.701701602892 : ℝ))
    <;> norm_num

theorem hsGroup5Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4923851395 : ℝ) 0.49778266275) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.656310879937 : ℝ)) (D := (1.549353574663 : ℝ))
    (Q := (0.677314918943 : ℝ)) (K := (0.825551080770 : ℝ))
    (A := (0.701701602891 : ℝ)) (T := (0.705537144841 : ℝ))
    <;> norm_num

theorem hsGroup5Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.49778266275 : ℝ) 0.503180186) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  apply hs_interval_12224 hw (C := (0.642291460432 : ℝ)) (D := (1.539668981626 : ℝ))
    (Q := (0.675285214035 : ℝ)) (K := (0.824321154379 : ℝ))
    (A := (0.705537144840 : ℝ)) (T := (0.709351947908 : ℝ))
    <;> norm_num

theorem hsGroup5_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.503180186) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.171664812389 := by
  by_cases h0 : θ ≤ 0.46539752325
  · apply hsGroup5Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4707950465
  · apply hsGroup5Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.47619256975
  · apply hsGroup5Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.481590093
  · apply hsGroup5Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.48698761625
  · apply hsGroup5Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.4923851395
  · apply hsGroup5Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.49778266275
  · apply hsGroup5Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup5Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup6Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4662971105) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682859510076 : ℝ))
    <;> norm_num

theorem hsGroup6Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4662971105 : ℝ) 0.472594221) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.728646768468 : ℝ)) (D := (1.598390899969 : ℝ))
    (Q := (0.687214633269 : ℝ)) (K := (0.831524200564 : ℝ))
    (A := (0.682859510075 : ℝ)) (T := (0.687454886520 : ℝ))
    <;> norm_num

theorem hsGroup6Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.472594221 : ℝ) 0.4788913315) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.710455189474 : ℝ)) (D := (1.586201312962 : ℝ))
    (Q := (0.684810950703 : ℝ)) (K := (0.830077808786 : ℝ))
    (A := (0.687454886519 : ℝ)) (T := (0.692019747912 : ℝ))
    <;> norm_num

theorem hsGroup6Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4788913315 : ℝ) 0.485188442) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.692742025417 : ℝ)) (D := (1.574241603809 : ℝ))
    (Q := (0.682416420316 : ℝ)) (K := (0.828634445731 : ℝ))
    (A := (0.692019747911 : ℝ)) (T := (0.696554694192 : ℝ))
    <;> norm_num

theorem hsGroup6Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.485188442 : ℝ) 0.4914855525) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.675488648698 : ℝ)) (D := (1.562504331380 : ℝ))
    (Q := (0.680030785333 : ℝ)) (K := (0.827193972044 : ℝ))
    (A := (0.696554694191 : ℝ)) (T := (0.701060305894 : ℝ))
    <;> norm_num

theorem hsGroup6Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4914855525 : ℝ) 0.497782663) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.658677386379 : ℝ)) (D := (1.550982388150 : ℝ))
    (Q := (0.677653796945 : ℝ)) (K := (0.825756252201 : ℝ))
    (A := (0.701060305893 : ℝ)) (T := (0.705537145018 : ℝ))
    <;> norm_num

theorem hsGroup6Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.497782663 : ℝ) 0.5040797735) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.642291459790 : ℝ)) (D := (1.539668981181 : ℝ))
    (Q := (0.675285213941 : ℝ)) (K := (0.824321154322 : ℝ))
    (A := (0.705537145017 : ℝ)) (T := (0.709985755844 : ℝ))
    <;> norm_num

theorem hsGroup6Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.5040797735 : ℝ) 0.510376884) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  apply hs_interval_12224 hw (C := (0.626314928681 : ℝ)) (D := (1.528557614416 : ℝ))
    (Q := (0.672924802369 : ℝ)) (K := (0.822888550004 : ℝ))
    (A := (0.709985755843 : ℝ)) (T := (0.714406665703 : ℝ))
    <;> norm_num

theorem hsGroup6_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.510376884) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.174112862129 := by
  by_cases h0 : θ ≤ 0.4662971105
  · apply hsGroup6Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.472594221
  · apply hsGroup6Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4788913315
  · apply hsGroup6Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.485188442
  · apply hsGroup6Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4914855525
  · apply hsGroup6Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.497782663
  · apply hsGroup6Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.5040797735
  · apply hsGroup6Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup6Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup7Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46719669775) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.683517884002 : ℝ))
    <;> norm_num

theorem hsGroup7Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.46719669775 : ℝ) 0.4743933955) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.726017947464 : ℝ)) (D := (1.596635164695 : ℝ))
    (Q := (0.686870679739 : ℝ)) (K := (0.831317382338 : ℝ))
    (A := (0.683517884001 : ℝ)) (T := (0.688762219856 : ℝ))
    <;> norm_num

theorem hsGroup7Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4743933955 : ℝ) 0.48159009325) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.705346300560 : ℝ)) (D := (1.582761128013 : ℝ))
    (Q := (0.684125876623 : ℝ)) (K := (0.829665116440 : ℝ))
    (A := (0.688762219855 : ℝ)) (T := (0.693966925185 : ℝ))
    <;> norm_num

theorem hsGroup7Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.48159009325 : ℝ) 0.488786791) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.685292471990 : ℝ)) (D := (1.569184528703 : ℝ))
    (Q := (0.681392930735 : ℝ)) (K := (0.828016754028 : ℝ))
    (A := (0.693966925184 : ℝ)) (T := (0.699132885080 : ℝ))
    <;> norm_num

theorem hsGroup7Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.488786791 : ℝ) 0.49598348875) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.665829172239 : ℝ)) (D := (1.555894439409 : ℝ))
    (Q := (0.678671463075 : ℝ)) (K := (0.826372089150 : ℝ))
    (A := (0.699132885079 : ℝ)) (T := (0.704260952170 : ℝ))
    <;> norm_num

theorem hsGroup7Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.49598348875 : ℝ) 0.5031801865) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.646930695667 : ℝ)) (D := (1.542880487814 : ℝ))
    (Q := (0.675961107957 : ℝ)) (K := (0.824730922250 : ℝ))
    (A := (0.704260952169 : ℝ)) (T := (0.709351948260 : ℝ))
    <;> norm_num

theorem hsGroup7Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.5031801865 : ℝ) 0.51037688425) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.628572807248 : ℝ)) (D := (1.530132820860 : ℝ))
    (Q := (0.673261512328 : ℝ)) (K := (0.823093059824 : ℝ))
    (A := (0.709351948259 : ℝ)) (T := (0.714406665878 : ℝ))
    <;> norm_num

theorem hsGroup7Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.51037688425 : ℝ) 0.517573582) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  apply hs_interval_12224 hw (C := (0.610732638883 : ℝ)) (D := (1.517642071743 : ℝ))
    (Q := (0.670572335115 : ℝ)) (K := (0.821458314098 : ℝ))
    (A := (0.714406665877 : ℝ)) (T := (0.719425869705 : ℝ))
    <;> norm_num

theorem hsGroup7_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.517573582) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.176543752714 := by
  by_cases h0 : θ ≤ 0.46719669775
  · apply hsGroup7Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4743933955
  · apply hsGroup7Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.48159009325
  · apply hsGroup7Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.488786791
  · apply hsGroup7Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.49598348875
  · apply hsGroup7Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.5031801865
  · apply hsGroup7Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.51037688425
  · apply hsGroup7Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup7Cell7_12224
  exact ⟨by linarith, hw.2⟩

theorem hsGroup8Cell0_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.468096284875) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.747336409998 : ℝ)) (D := (1.610818160004 : ℝ))
    (Q := (0.689627733136 : ℝ)) (K := (0.832973764442 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.684175624292 : ℝ))
    <;> norm_num

theorem hsGroup8Cell1_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.468096284875 : ℝ) 0.47619256975) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.723399230957 : ℝ)) (D := (1.594884256328 : ℝ))
    (Q := (0.686526917648 : ℝ)) (K := (0.831110628447 : ℝ))
    (A := (0.684175624291 : ℝ)) (T := (0.690067076269 : ℝ))
    <;> norm_num

theorem hsGroup8Cell2_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.47619256975 : ℝ) 0.484288854625) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.700276017665 : ℝ)) (D := (1.579339530477 : ℝ))
    (Q := (0.683441543647 : ℝ)) (K := (0.829252668086 : ℝ))
    (A := (0.690067076268 : ℝ)) (T := (0.695908653938 : ℝ))
    <;> norm_num

theorem hsGroup8Cell3_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.484288854625 : ℝ) 0.4923851395) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.677925946766 : ℝ)) (D := (1.564167739180 : ℝ))
    (Q := (0.680371055289 : ℝ)) (K := (0.827399582313 : ℝ))
    (A := (0.695908653937 : ℝ)) (T := (0.701701602892 : ℝ))
    <;> norm_num

theorem hsGroup8Cell4_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.4923851395 : ℝ) 0.500481424375) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.656310879937 : ℝ)) (D := (1.549353574663 : ℝ))
    (Q := (0.677314918943 : ℝ)) (K := (0.825551080770 : ℝ))
    (A := (0.701701602891 : ℝ)) (T := (0.707447117724 : ℝ))
    <;> norm_num

theorem hsGroup8Cell5_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.500481424375 : ℝ) 0.50857770925) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.635395146711 : ℝ)) (D := (1.534882596387 : ℝ))
    (Q := (0.674272621891 : ℝ)) (K := (0.823706883138 : ℝ))
    (A := (0.707447117723 : ℝ)) (T := (0.713146344905 : ℝ))
    <;> norm_num

theorem hsGroup8Cell6_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.50857770925 : ℝ) 0.516673994125) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.615145348037 : ℝ)) (D := (1.520741168785 : ℝ))
    (Q := (0.671243671120 : ℝ)) (K := (0.821866718529 : ℝ))
    (A := (0.713146344904 : ℝ)) (T := (0.718800385452 : ℝ))
    <;> norm_num

theorem hsGroup8Cell7_12224 {θ : ℝ}
    (hw : θ ∈ Icc (0.516673994125 : ℝ) 0.524770279) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  apply hs_interval_12224 hw (C := (0.595530178319 : ℝ)) (D := (1.506916404384 : ℝ))
    (Q := (0.668227592207 : ℝ)) (K := (0.820030324924 : ℝ))
    (A := (0.718800385451 : ℝ)) (T := (0.724410297415 : ℝ))
    <;> norm_num

theorem hsGroup8_12224 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.524770279) :
    hsProfile 12224 θ 0.006 * (θ * √θ) ≤ 0.178957150965 := by
  by_cases h0 : θ ≤ 0.468096284875
  · apply hsGroup8Cell0_12224
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47619256975
  · apply hsGroup8Cell1_12224
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.484288854625
  · apply hsGroup8Cell2_12224
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4923851395
  · apply hsGroup8Cell3_12224
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.500481424375
  · apply hsGroup8Cell4_12224
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.50857770925
  · apply hsGroup8Cell5_12224
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.516673994125
  · apply hsGroup8Cell6_12224
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup8Cell7_12224
  exact ⟨by linarith, hw.2⟩

end BstLean.Part281.HS12224

namespace BstLean.Part281.HS12000
open Real Set BstLean.Part194 BstLean.Part211 BstLean.Part253

theorem S0_lower_12000 : (11239 : ℝ) ≤ S0 12000 := by
  have hs : √(12 * (12000 - 1 : ℝ)) ≤ 380 := sqrt_le_iff.mpr (by norm_num)
  unfold S0
  simp only [Nat.cast_ofNat]
  linarith

theorem a0_upper_12000 : a0 12000 ≤ 0.00604276 := by
  have hs24 : √(24 : ℝ) ≤ 4.89897949 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hn : (109.544511 : ℝ) ≤ √12000 := le_sqrt_of_sq_le (by norm_num)
  have hn2 : (10.46635 : ℝ) ≤ √(√12000) := le_sqrt_of_sq_le (by linarith)
  unfold a0
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (4.89897949 : ℝ) / (1.414213562 * 109.544511 * 10.46635) := by gcongr
    _ ≤ (0.00604276 : ℝ) := by norm_num

theorem hs_interval_12000 {θ a b C D Q K A T S : ℝ}
    (hw : θ ∈ Icc a b) (ha : 0 < a) (hb : b ≤ 1)
    (hC : 2 * (1 - a) / (3.141592 * a) ≤ C) (hC0 : 0 ≤ C)
    (hD : 1 + 2 * C * 12000 / 11239 ≤ D ^ 2) (hD0 : 0 < D)
    (hQ : 1 - ((1 - 0.00000615) * (1 - 1 / 11239)) / D / 2 ≤ Q)
    (hCH : (1 + 0.006) * (Q ^ 2 + 1 / 12000) +
      (1 + 1 / 0.006) * (3 / (16 * 12000)) + 4 * (1 + 2 / 12000) / 12000 ≤ K ^ 4)
    (hK : 0 ≤ K) (hA : 0 < A) (hAsq : A ^ 2 ≤ a)
    (hT : 0 ≤ T) (hTsq : b ≤ T ^ 2)
    (hS : (K + 0.00604276 / A) ^ 4 * (b * T) ≤ S) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ S := by
  have hθ := ha.trans_le hw.1
  have hθ1 := hw.2.trans hb
  have hlo := hw.1
  have hhi := hw.2
  have hb0 : 0 ≤ b := hθ.le.trans hhi
  have hj := J0_bounds (by norm_num : 64 ≤ 12000) hθ hθ1
  have hc : axialC θ ≤ C := by
    unfold axialC
    apply le_trans ?_ hC
    apply div_le_div₀ (by have := hw.1; have := hw.2; nlinarith : 0 ≤ 2 * (1 - a))
      (by have := hw.1; linarith) (mul_pos (by norm_num) ha)
    have hp := pi_gt_d6.le
    gcongr
  have hs0 := S0_lower_12000
  have hd : √(1 + 2 * axialC θ * 12000 / S0 12000) ≤ D := by
    apply sqrt_le_iff.mpr
    refine ⟨hD0.le, ?_⟩
    apply le_trans ?_ hD
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    gcongr
  have hden : 0 < √(1 + 2 * axialC θ * 12000 / S0 12000) := by
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    have hspos : 0 < S0 12000 := by linarith
    positivity
  have hn : (1 - 0.00000615 : ℝ) * (1 - 1 / 11239) ≤
      (1 - exp (-12)) * (1 - 1 / S0 12000) := by
    have he := exp_minus_twelve_upper
    have he0 : 0 ≤ 1 - exp (-12 : ℝ) := by linarith
    have hs : (1 : ℝ) / S0 12000 ≤ 1 / 11239 := by
      gcongr
    gcongr
  have hJ : ((1 - 0.00000615 : ℝ) * (1 - 1 / 11239)) / D ≤ J0 12000 θ := by
    unfold J0
    simp only [Nat.cast_ofNat]
    exact div_le_div₀ (le_trans (by norm_num) hn) hn hden hd
  have hq : qHS 12000 θ ≤ Q := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS 12000 θ := by linarith [hj.2.2.1]
  have hqQ : 0 ≤ Q := hq0.trans hq
  have hch : CH 12000 θ 0.006 ≤ K ^ 4 := by
    unfold CH
    simp only [Nat.cast_ofNat]
    apply le_trans ?_ hCH
    gcongr
  have hroot : √(√(CH 12000 θ 0.006)) ≤ K := by
    apply sqrt_le_iff.mpr
    refine ⟨hK, sqrt_le_iff.mpr ⟨sq_nonneg K, ?_⟩⟩
    simpa only [← pow_mul] using hch
  have hθroot : A ≤ √θ := le_sqrt_of_sq_le (hAsq.trans hw.1)
  have hθroot1 : √θ ≤ T := sqrt_le_iff.mpr ⟨hT, hw.2.trans hTsq⟩
  rw [hsProfile_eq_paper (by norm_num) hθ]
  have ha0 : 0 ≤ a0 12000 := by unfold a0; positivity
  have ha0u := a0_upper_12000
  apply le_trans ?_ hS
  gcongr


theorem hsGroup1Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.461803041375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.679560918076 : ℝ))
    <;> norm_num

theorem hsGroup1Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.461803041375 : ℝ) 0.46360608275) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.741932958151 : ℝ)) (D := (1.607588082384 : ℝ))
    (Q := (0.689004638186 : ℝ)) (K := (0.832623810856 : ℝ))
    (A := (0.679560918075 : ℝ)) (T := (0.680886248026 : ℝ))
    <;> norm_num

theorem hsGroup1Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.46360608275 : ℝ) 0.465409124125) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.736571536155 : ℝ)) (D := (1.604023237952 : ℝ))
    (Q := (0.688313469843 : ℝ)) (K := (0.832208728400 : ℝ))
    (A := (0.680886248025 : ℝ)) (T := (0.682209003258 : ℝ))
    <;> norm_num

theorem hsGroup1Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.465409124125 : ℝ) 0.4672121655) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.731251655526 : ℝ)) (D := (1.600478166511 : ℝ))
    (Q := (0.687623081783 : ℝ)) (K := (0.831793910396 : ℝ))
    (A := (0.682209003257 : ℝ)) (T := (0.683529198718 : ℝ))
    <;> norm_num

theorem hsGroup1Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4672121655 : ℝ) 0.469015206875) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.725972835322 : ℝ)) (D := (1.596952678188 : ℝ))
    (Q := (0.686933467624 : ℝ)) (K := (0.831379353403 : ℝ))
    (A := (0.683529198717 : ℝ)) (T := (0.684846849212 : ℝ))
    <;> norm_num

theorem hsGroup1Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.469015206875 : ℝ) 0.47081824825) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.720734601994 : ℝ)) (D := (1.593446585657 : ℝ))
    (Q := (0.686244621044 : ℝ)) (K := (0.830965054006 : ℝ))
    (A := (0.684846849211 : ℝ)) (T := (0.686161969400 : ℝ))
    <;> norm_num

theorem hsGroup1Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47081824825 : ℝ) 0.472621289625) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.715536489251 : ℝ)) (D := (1.589959704102 : ℝ))
    (Q := (0.685556535779 : ℝ)) (K := (0.830551008820 : ℝ))
    (A := (0.686161969399 : ℝ)) (T := (0.687474573803 : ℝ))
    <;> norm_num

theorem hsGroup1Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.472621289625 : ℝ) 0.474424331) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  apply hs_interval_12000 hw (C := (0.710378037912 : ℝ)) (D := (1.586491851161 : ℝ))
    (Q := (0.684869205623 : ℝ)) (K := (0.830137214488 : ℝ))
    (A := (0.687474573802 : ℝ)) (T := (0.688784676805 : ℝ))
    <;> norm_num

theorem hsGroup1_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.474424331) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.161862832674 := by
  by_cases h0 : θ ≤ 0.461803041375
  · apply hsGroup1Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46360608275
  · apply hsGroup1Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.465409124125
  · apply hsGroup1Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4672121655
  · apply hsGroup1Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.469015206875
  · apply hsGroup1Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.47081824825
  · apply hsGroup1Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.472621289625
  · apply hsGroup1Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup1Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup2Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.462704562125) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680223905876 : ℝ))
    <;> norm_num

theorem hsGroup2Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.462704562125 : ℝ) 0.46540912425) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.739247023945 : ℝ)) (D := (1.605803176453 : ℝ))
    (Q := (0.688658956054 : ℝ)) (K := (0.832416236341 : ℝ))
    (A := (0.680223905875 : ℝ)) (T := (0.682209003349 : ℝ))
    <;> norm_num

theorem hsGroup2Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.46540912425 : ℝ) 0.468113686375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.731251655159 : ℝ)) (D := (1.600478166266 : ℝ))
    (Q := (0.687623081735 : ℝ)) (K := (0.831793910367 : ℝ))
    (A := (0.682209003348 : ℝ)) (T := (0.684188341304 : ℝ))
    <;> norm_num

theorem hsGroup2Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.468113686375 : ℝ) 0.4708182485) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.723348674066 : ℝ)) (D := (1.595197218693 : ℝ))
    (Q := (0.686588948708 : ℝ)) (K := (0.831172171674 : ℝ))
    (A := (0.684188341303 : ℝ)) (T := (0.686161969582 : ℝ))
    <;> norm_num

theorem hsGroup2Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4708182485 : ℝ) 0.473522810625) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.715536488533 : ℝ)) (D := (1.589959703620 : ℝ))
    (Q := (0.685556535684 : ℝ)) (K := (0.830551008763 : ℝ))
    (A := (0.686161969581 : ℝ)) (T := (0.688129937312 : ℝ))
    <;> norm_num

theorem hsGroup2Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.473522810625 : ℝ) 0.47622737275) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.707813542802 : ℝ)) (D := (1.584765003499 : ℝ))
    (Q := (0.684525821667 : ℝ)) (K := (0.829930410278 : ℝ))
    (A := (0.688129937311 : ℝ)) (T := (0.690092292922 : ℝ))
    <;> norm_num

theorem hsGroup2Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47622737275 : ℝ) 0.478931934875) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.700178316459 : ℝ)) (D := (1.579612513038 : ℝ))
    (Q := (0.683496785951 : ℝ)) (K := (0.829310365001 : ℝ))
    (A := (0.690092292921 : ℝ)) (T := (0.692049084152 : ℝ))
    <;> norm_num

theorem hsGroup2Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.478931934875 : ℝ) 0.481636497) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  apply hs_interval_12000 hw (C := (0.692629323429 : ℝ)) (D := (1.574501638878 : ℝ))
    (Q := (0.682469408107 : ℝ)) (K := (0.828690861850 : ℝ))
    (A := (0.692049084151 : ℝ)) (T := (0.694000358070 : ℝ))
    <;> norm_num

theorem hsGroup2_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.481636497) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.164383301470 := by
  by_cases h0 : θ ≤ 0.462704562125
  · apply hsGroup2Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46540912425
  · apply hsGroup2Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.468113686375
  · apply hsGroup2Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4708182485
  · apply hsGroup2Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.473522810625
  · apply hsGroup2Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.47622737275
  · apply hsGroup2Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.478931934875
  · apply hsGroup2Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup2Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup3Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46360608275) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680886248026 : ℝ))
    <;> norm_num

theorem hsGroup3Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.46360608275 : ℝ) 0.4672121655) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.736571536155 : ℝ)) (D := (1.604023237952 : ℝ))
    (Q := (0.688313469843 : ℝ)) (K := (0.832208728400 : ℝ))
    (A := (0.680886248025 : ℝ)) (T := (0.683529198718 : ℝ))
    <;> norm_num

theorem hsGroup3Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4672121655 : ℝ) 0.47081824825) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.725972835322 : ℝ)) (D := (1.596952678188 : ℝ))
    (Q := (0.686933467624 : ℝ)) (K := (0.831379353403 : ℝ))
    (A := (0.683529198717 : ℝ)) (T := (0.686161969400 : ℝ))
    <;> norm_num

theorem hsGroup3Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47081824825 : ℝ) 0.474424331) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.715536489251 : ℝ)) (D := (1.589959704102 : ℝ))
    (Q := (0.685556535779 : ℝ)) (K := (0.830551008820 : ℝ))
    (A := (0.686161969399 : ℝ)) (T := (0.688784676805 : ℝ))
    <;> norm_num

theorem hsGroup3Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.474424331 : ℝ) 0.47803041375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.705258795782 : ℝ)) (D := (1.583042846897 : ℝ))
    (Q := (0.684182624425 : ℝ)) (K := (0.829723667678 : ℝ))
    (A := (0.688784676804 : ℝ)) (T := (0.691397435453 : ℝ))
    <;> norm_num

theorem hsGroup3Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47803041375 : ℝ) 0.4816364965) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.695136164469 : ℝ)) (D := (1.576200676495 : ℝ))
    (Q := (0.682811684588 : ℝ)) (K := (0.828897303438 : ℝ))
    (A := (0.691397435452 : ℝ)) (T := (0.694000357709 : ℝ))
    <;> norm_num

theorem hsGroup3Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4816364965 : ℝ) 0.48524257925) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.685165112392 : ℝ)) (D := (1.569431800234 : ℝ))
    (Q := (0.681443668177 : ℝ)) (K := (0.828071889990 : ℝ))
    (A := (0.694000357708 : ℝ)) (T := (0.696593553839 : ℝ))
    <;> norm_num

theorem hsGroup3Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.48524257925 : ℝ) 0.488848662) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  apply hs_interval_12000 hw (C := (0.675342260166 : ℝ)) (D := (1.562734861616 : ℝ))
    (Q := (0.680078527965 : ℝ)) (K := (0.827247401638 : ℝ))
    (A := (0.696593553838 : ℝ)) (T := (0.699177132064 : ℝ))
    <;> norm_num

theorem hsGroup3_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.488848662) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.166887933819 := by
  by_cases h0 : θ ≤ 0.46360608275
  · apply hsGroup3Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4672121655
  · apply hsGroup3Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.47081824825
  · apply hsGroup3Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.474424331
  · apply hsGroup3Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.47803041375
  · apply hsGroup3Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.4816364965
  · apply hsGroup3Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.48524257925
  · apply hsGroup3Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup3Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup4Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4645076035) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.681547946590 : ℝ))
    <;> norm_num

theorem hsGroup4Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4645076035 : ℝ) 0.469015207) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.733906433219 : ℝ)) (D := (1.602248242412 : ℝ))
    (Q := (0.687968178654 : ℝ)) (K := (0.832001286543 : ℝ))
    (A := (0.681547946589 : ℝ)) (T := (0.684846849303 : ℝ))
    <;> norm_num

theorem hsGroup4Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.469015207 : ℝ) 0.4735228105) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.720734601633 : ℝ)) (D := (1.593446585415 : ℝ))
    (Q := (0.686244620996 : ℝ)) (K := (0.830965053977 : ℝ))
    (A := (0.684846849302 : ℝ)) (T := (0.688129937222 : ℝ))
    <;> norm_num

theorem hsGroup4Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4735228105 : ℝ) 0.478030414) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.707813543157 : ℝ)) (D := (1.584765003738 : ℝ))
    (Q := (0.684525821715 : ℝ)) (K := (0.829930410307 : ℝ))
    (A := (0.688129937221 : ℝ)) (T := (0.691397435634 : ℝ))
    <;> norm_num

theorem hsGroup4Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.478030414 : ℝ) 0.4825380175) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.695136163773 : ℝ)) (D := (1.576200676024 : ℝ))
    (Q := (0.682811684493 : ℝ)) (K := (0.828897303381 : ℝ))
    (A := (0.691397435633 : ℝ)) (T := (0.694649564529 : ℝ))
    <;> norm_num

theorem hsGroup4Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4825380175 : ℝ) 0.487045621) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.682695634533 : ℝ)) (D := (1.567750873055 : ℝ))
    (Q := (0.681102115188 : ℝ)) (K := (0.827865682098 : ℝ))
    (A := (0.694649564528 : ℝ)) (T := (0.697886538773 : ℝ))
    <;> norm_num

theorem hsGroup4Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.487045621 : ℝ) 0.4915532245) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.670485379300 : ℝ)) (D := (1.559412953920 : ℝ))
    (Q := (0.679397021762 : ℝ)) (K := (0.826835496367 : ℝ))
    (A := (0.697886538772 : ℝ)) (T := (0.701108568269 : ℝ))
    <;> norm_num

theorem hsGroup4Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4915532245 : ℝ) 0.496060828) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  apply hs_interval_12000 hw (C := (0.658499063149 : ℝ)) (D := (1.551184362358 : ℝ))
    (Q := (0.677696314209 : ℝ)) (K := (0.825806697075 : ℝ))
    (A := (0.701108568268 : ℝ)) (T := (0.704315858121 : ℝ))
    <;> norm_num

theorem hsGroup4_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.496060828) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.169376361898 := by
  by_cases h0 : θ ≤ 0.4645076035
  · apply hsGroup4Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.469015207
  · apply hsGroup4Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4735228105
  · apply hsGroup4Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.478030414
  · apply hsGroup4Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4825380175
  · apply hsGroup4Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.487045621
  · apply hsGroup4Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.4915532245
  · apply hsGroup4Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup4Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup5Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.465409124125) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682209003258 : ℝ))
    <;> norm_num

theorem hsGroup5Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.465409124125 : ℝ) 0.47081824825) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.731251655526 : ℝ)) (D := (1.600478166511 : ℝ))
    (Q := (0.687623081783 : ℝ)) (K := (0.831793910396 : ℝ))
    (A := (0.682209003257 : ℝ)) (T := (0.686161969400 : ℝ))
    <;> norm_num

theorem hsGroup5Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47081824825 : ℝ) 0.476227372375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.715536489251 : ℝ)) (D := (1.589959704102 : ℝ))
    (Q := (0.685556535779 : ℝ)) (K := (0.830551008820 : ℝ))
    (A := (0.686161969399 : ℝ)) (T := (0.690092292651 : ℝ))
    <;> norm_num

theorem hsGroup5Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.476227372375 : ℝ) 0.4816364965) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.700178317511 : ℝ)) (D := (1.579612513749 : ℝ))
    (Q := (0.683496786093 : ℝ)) (K := (0.829310365087 : ℝ))
    (A := (0.690092292650 : ℝ)) (T := (0.694000357709 : ℝ))
    <;> norm_num

theorem hsGroup5Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4816364965 : ℝ) 0.487045620625) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.685165112392 : ℝ)) (D := (1.569431800234 : ℝ))
    (Q := (0.681443668177 : ℝ)) (K := (0.828071889990 : ℝ))
    (A := (0.694000357708 : ℝ)) (T := (0.697886538504 : ℝ))
    <;> norm_num

theorem hsGroup5Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.487045620625 : ℝ) 0.49245474475) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.670485380306 : ℝ)) (D := (1.559412954608 : ℝ))
    (Q := (0.679397021904 : ℝ)) (K := (0.826835496453 : ℝ))
    (A := (0.697886538503 : ℝ)) (T := (0.701751198610 : ℝ))
    <;> norm_num

theorem hsGroup5Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.49245474475 : ℝ) 0.497863868875) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.656128132646 : ℝ)) (D := (1.549551544972 : ℝ))
    (Q := (0.677356691392 : ℝ)) (K := (0.825601099437 : ℝ))
    (A := (0.701751198609 : ℝ)) (T := (0.705594691644 : ℝ))
    <;> norm_num

theorem hsGroup5Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.497863868875 : ℝ) 0.503272993) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  apply hs_interval_12000 hw (C := (0.642082858357 : ℝ)) (D := (1.539843307818 : ℝ))
    (Q := (0.675322524837 : ℝ)) (K := (0.824368615857 : ℝ))
    (A := (0.705594691643 : ℝ)) (T := (0.709417361643 : ℝ))
    <;> norm_num

theorem hsGroup5_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.503272993) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.171848225245 := by
  by_cases h0 : θ ≤ 0.465409124125
  · apply hsGroup5Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47081824825
  · apply hsGroup5Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.476227372375
  · apply hsGroup5Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4816364965
  · apply hsGroup5Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.487045620625
  · apply hsGroup5Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.49245474475
  · apply hsGroup5Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.497863868875
  · apply hsGroup5Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup5Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup6Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.466310644875) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682869420077 : ℝ))
    <;> norm_num

theorem hsGroup6Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.466310644875 : ℝ) 0.47262128975) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.728607142456 : ℝ)) (D := (1.598712986104 : ℝ))
    (Q := (0.687278178338 : ℝ)) (K := (0.831586599473 : ℝ))
    (A := (0.682869420076 : ℝ)) (T := (0.687474573894 : ℝ))
    <;> norm_num

theorem hsGroup6Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.47262128975 : ℝ) 0.478931934625) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.710378037556 : ℝ)) (D := (1.586491850921 : ℝ))
    (Q := (0.684869205575 : ℝ)) (K := (0.830137214459 : ℝ))
    (A := (0.687474573893 : ℝ)) (T := (0.692049083971 : ℝ))
    <;> norm_num

theorem hsGroup6Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.478931934625 : ℝ) 0.4852425795) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.692629324123 : ℝ)) (D := (1.574501639349 : ℝ))
    (Q := (0.682469408202 : ℝ)) (K := (0.828690861907 : ℝ))
    (A := (0.692049083970 : ℝ)) (T := (0.696593554019 : ℝ))
    <;> norm_num

theorem hsGroup6Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4852425795 : ℝ) 0.491553224375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.675342259490 : ℝ)) (D := (1.562734861154 : ℝ))
    (Q := (0.680078527870 : ℝ)) (K := (0.827247401581 : ℝ))
    (A := (0.696593554018 : ℝ)) (T := (0.701108568180 : ℝ))
    <;> norm_num

theorem hsGroup6Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.491553224375 : ℝ) 0.49786386925) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.658499063479 : ℝ)) (D := (1.551184362585 : ℝ))
    (Q := (0.677696314256 : ℝ)) (K := (0.825806697103 : ℝ))
    (A := (0.701108568179 : ℝ)) (T := (0.705594691909 : ℝ))
    <;> norm_num

theorem hsGroup6Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.49786386925 : ℝ) 0.504174514125) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.642082857394 : ℝ)) (D := (1.539843307151 : ℝ))
    (Q := (0.675322524696 : ℝ)) (K := (0.824368615771 : ℝ))
    (A := (0.705594691908 : ℝ)) (T := (0.710052472797 : ℝ))
    <;> norm_num

theorem hsGroup6Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.504174514125 : ℝ) 0.510485159) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  apply hs_interval_12000 hw (C := (0.626077607611 : ℝ)) (D := (1.528705157728 : ℝ))
    (Q := (0.672956923837 : ℝ)) (K := (0.822933028381 : ℝ))
    (A := (0.710052472796 : ℝ)) (T := (0.714482441352 : ℝ))
    <;> norm_num

theorem hsGroup6_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.510485159) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.174303173207 := by
  by_cases h0 : θ ≤ 0.466310644875
  · apply hsGroup6Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47262128975
  · apply hsGroup6Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.478931934625
  · apply hsGroup6Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4852425795
  · apply hsGroup6Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.491553224375
  · apply hsGroup6Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.49786386925
  · apply hsGroup6Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.504174514125
  · apply hsGroup6Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup6Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup7Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4672121655) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.683529198718 : ℝ))
    <;> norm_num

theorem hsGroup7Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4672121655 : ℝ) 0.474424331) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.725972835322 : ℝ)) (D := (1.596952678188 : ℝ))
    (Q := (0.686933467624 : ℝ)) (K := (0.831379353403 : ℝ))
    (A := (0.683529198717 : ℝ)) (T := (0.688784676805 : ℝ))
    <;> norm_num

theorem hsGroup7Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.474424331 : ℝ) 0.4816364965) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.705258795782 : ℝ)) (D := (1.583042846897 : ℝ))
    (Q := (0.684182624425 : ℝ)) (K := (0.829723667678 : ℝ))
    (A := (0.688784676804 : ℝ)) (T := (0.694000357709 : ℝ))
    <;> norm_num

theorem hsGroup7Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4816364965 : ℝ) 0.488848662) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.685165112392 : ℝ)) (D := (1.569431800234 : ℝ))
    (Q := (0.681443668177 : ℝ)) (K := (0.828071889990 : ℝ))
    (A := (0.694000357708 : ℝ)) (T := (0.699177132064 : ℝ))
    <;> norm_num

theorem hsGroup7Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.488848662 : ℝ) 0.4960608275) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.665664328120 : ℝ)) (D := (1.556108539103 : ℝ))
    (Q := (0.678716217561 : ℝ)) (K := (0.826423813088 : ℝ))
    (A := (0.699177132063 : ℝ)) (T := (0.704315857766 : ℝ))
    <;> norm_num

theorem hsGroup7Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4960608275 : ℝ) 0.503272993) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.646730582710 : ℝ)) (D := (1.543062624205 : ℝ))
    (Q := (0.675999904679 : ℝ)) (K := (0.824779236163 : ℝ))
    (A := (0.704315857765 : ℝ)) (T := (0.709417361643 : ℝ))
    <;> norm_num

theorem hsGroup7Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.503272993 : ℝ) 0.5104851585) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.628339498270 : ℝ)) (D := (1.530284139877 : ℝ))
    (Q := (0.673294374358 : ℝ)) (K := (0.823137964507 : ℝ))
    (A := (0.709417361642 : ℝ)) (T := (0.714482441002 : ℝ))
    <;> norm_num

theorem hsGroup7Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.5104851585 : ℝ) 0.517697324) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  apply hs_interval_12000 hw (C := (0.610468074559 : ℝ)) (D := (1.517763660749 : ℝ))
    (Q := (0.670599283500 : ℝ)) (K := (0.821499809181 : ℝ))
    (A := (0.714482441001 : ℝ)) (T := (0.719511865087 : ℝ))
    <;> norm_num

theorem hsGroup7_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.517697324) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.176740861924 := by
  by_cases h0 : θ ≤ 0.4672121655
  · apply hsGroup7Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.474424331
  · apply hsGroup7Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4816364965
  · apply hsGroup7Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.488848662
  · apply hsGroup7Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4960608275
  · apply hsGroup7Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.503272993
  · apply hsGroup7Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.5104851585
  · apply hsGroup7Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup7Cell7_12000
  exact ⟨by linarith, hw.2⟩

theorem hsGroup8Cell0_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46811368625) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.747336409998 : ℝ)) (D := (1.611172892273 : ℝ))
    (Q := (0.689696593254 : ℝ)) (K := (0.833039161237 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.684188341212 : ℝ))
    <;> norm_num

theorem hsGroup8Cell1_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.46811368625 : ℝ) 0.4762273725) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.723348674429 : ℝ)) (D := (1.595197218936 : ℝ))
    (Q := (0.686588948755 : ℝ)) (K := (0.831172171703 : ℝ))
    (A := (0.684188341211 : ℝ)) (T := (0.690092292741 : ℝ))
    <;> norm_num

theorem hsGroup8Cell2_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.4762273725 : ℝ) 0.48434105875) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.700178317160 : ℝ)) (D := (1.579612513512 : ℝ))
    (Q := (0.683496786046 : ℝ)) (K := (0.829310365059 : ℝ))
    (A := (0.690092292740 : ℝ)) (T := (0.695946160813 : ℝ))
    <;> norm_num

theorem hsGroup8Cell3_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.48434105875 : ℝ) 0.492454745) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.677784260004 : ℝ)) (D := (1.564402424627 : ℝ))
    (Q := (0.680419545854 : ℝ)) (K := (0.827453438346 : ℝ))
    (A := (0.695946160812 : ℝ)) (T := (0.701751198788 : ℝ))
    <;> norm_num

theorem hsGroup8Cell4_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.492454745 : ℝ) 0.50056843125) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.656128131990 : ℝ)) (D := (1.549551544520 : ℝ))
    (Q := (0.677356691297 : ℝ)) (K := (0.825601099379 : ℝ))
    (A := (0.701751198787 : ℝ)) (T := (0.707508608605 : ℝ))
    <;> norm_num

theorem hsGroup8Cell5_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.50056843125 : ℝ) 0.5086821175) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.635174049958 : ℝ)) (D := (1.535045340052 : ℝ))
    (Q := (0.674307706564 : ℝ)) (K := (0.823753066086 : ℝ))
    (A := (0.707508608604 : ℝ)) (T := (0.713219543690 : ℝ))
    <;> norm_num

theorem hsGroup8Cell6_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.5086821175 : ℝ) 0.51679580375) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.614888420154 : ℝ)) (D := (1.520870089794 : ℝ))
    (Q := (0.671272095701 : ℝ)) (K := (0.821909065896 : ℝ))
    (A := (0.713219543689 : ℝ)) (T := (0.718885111649 : ℝ))
    <;> norm_num

theorem hsGroup8Cell7_12000 {θ : ℝ}
    (hw : θ ∈ Icc (0.51679580375 : ℝ) 0.524909490) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  apply hs_interval_12000 hw (C := (0.595239758508 : ℝ)) (D := (1.507012826561 : ℝ))
    (Q := (0.668249381480 : ℝ)) (K := (0.820068835168 : ℝ))
    (A := (0.718885111648 : ℝ)) (T := (0.724506376784 : ℝ))
    <;> norm_num

theorem hsGroup8_12000 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.524909490) :
    hsProfile 12000 θ 0.006 * (θ * √θ) ≤ 0.179160956768 := by
  by_cases h0 : θ ≤ 0.46811368625
  · apply hsGroup8Cell0_12000
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4762273725
  · apply hsGroup8Cell1_12000
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.48434105875
  · apply hsGroup8Cell2_12000
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.492454745
  · apply hsGroup8Cell3_12000
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.50056843125
  · apply hsGroup8Cell4_12000
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.5086821175
  · apply hsGroup8Cell5_12000
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.51679580375
  · apply hsGroup8Cell6_12000
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup8Cell7_12000
  exact ⟨by linarith, hw.2⟩

end BstLean.Part281.HS12000

namespace BstLean.Part281.HS11883
open Real Set BstLean.Part194 BstLean.Part211 BstLean.Part253

theorem S0_lower_11883 : (11126 : ℝ) ≤ S0 11883 := by
  have hs : √(12 * (11883 - 1 : ℝ)) ≤ 378 := sqrt_le_iff.mpr (by norm_num)
  unfold S0
  simp only [Nat.cast_ofNat]
  linarith

theorem a0_upper_11883 : a0 11883 ≤ 0.00608733 := by
  have hs24 : √(24 : ℝ) ≤ 4.89897949 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hn : (109.009173 : ℝ) ≤ √11883 := le_sqrt_of_sq_le (by norm_num)
  have hn2 : (10.44074 : ℝ) ≤ √(√11883) := le_sqrt_of_sq_le (by linarith)
  unfold a0
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (4.89897949 : ℝ) / (1.414213562 * 109.009173 * 10.44074) := by gcongr
    _ ≤ (0.00608733 : ℝ) := by norm_num

theorem hs_interval_11883 {θ a b C D Q K A T S : ℝ}
    (hw : θ ∈ Icc a b) (ha : 0 < a) (hb : b ≤ 1)
    (hC : 2 * (1 - a) / (3.141592 * a) ≤ C) (hC0 : 0 ≤ C)
    (hD : 1 + 2 * C * 11883 / 11126 ≤ D ^ 2) (hD0 : 0 < D)
    (hQ : 1 - ((1 - 0.00000615) * (1 - 1 / 11126)) / D / 2 ≤ Q)
    (hCH : (1 + 0.006) * (Q ^ 2 + 1 / 11883) +
      (1 + 1 / 0.006) * (3 / (16 * 11883)) + 4 * (1 + 2 / 11883) / 11883 ≤ K ^ 4)
    (hK : 0 ≤ K) (hA : 0 < A) (hAsq : A ^ 2 ≤ a)
    (hT : 0 ≤ T) (hTsq : b ≤ T ^ 2)
    (hS : (K + 0.00608733 / A) ^ 4 * (b * T) ≤ S) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ S := by
  have hθ := ha.trans_le hw.1
  have hθ1 := hw.2.trans hb
  have hlo := hw.1
  have hhi := hw.2
  have hb0 : 0 ≤ b := hθ.le.trans hhi
  have hj := J0_bounds (by norm_num : 64 ≤ 11883) hθ hθ1
  have hc : axialC θ ≤ C := by
    unfold axialC
    apply le_trans ?_ hC
    apply div_le_div₀ (by have := hw.1; have := hw.2; nlinarith : 0 ≤ 2 * (1 - a))
      (by have := hw.1; linarith) (mul_pos (by norm_num) ha)
    have hp := pi_gt_d6.le
    gcongr
  have hs0 := S0_lower_11883
  have hd : √(1 + 2 * axialC θ * 11883 / S0 11883) ≤ D := by
    apply sqrt_le_iff.mpr
    refine ⟨hD0.le, ?_⟩
    apply le_trans ?_ hD
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    gcongr
  have hden : 0 < √(1 + 2 * axialC θ * 11883 / S0 11883) := by
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    have hspos : 0 < S0 11883 := by linarith
    positivity
  have hn : (1 - 0.00000615 : ℝ) * (1 - 1 / 11126) ≤
      (1 - exp (-12)) * (1 - 1 / S0 11883) := by
    have he := exp_minus_twelve_upper
    have he0 : 0 ≤ 1 - exp (-12 : ℝ) := by linarith
    have hs : (1 : ℝ) / S0 11883 ≤ 1 / 11126 := by
      gcongr
    gcongr
  have hJ : ((1 - 0.00000615 : ℝ) * (1 - 1 / 11126)) / D ≤ J0 11883 θ := by
    unfold J0
    simp only [Nat.cast_ofNat]
    exact div_le_div₀ (le_trans (by norm_num) hn) hn hden hd
  have hq : qHS 11883 θ ≤ Q := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS 11883 θ := by linarith [hj.2.2.1]
  have hqQ : 0 ≤ Q := hq0.trans hq
  have hch : CH 11883 θ 0.006 ≤ K ^ 4 := by
    unfold CH
    simp only [Nat.cast_ofNat]
    apply le_trans ?_ hCH
    gcongr
  have hroot : √(√(CH 11883 θ 0.006)) ≤ K := by
    apply sqrt_le_iff.mpr
    refine ⟨hK, sqrt_le_iff.mpr ⟨sq_nonneg K, ?_⟩⟩
    simpa only [← pow_mul] using hch
  have hθroot : A ≤ √θ := le_sqrt_of_sq_le (hAsq.trans hw.1)
  have hθroot1 : √θ ≤ T := sqrt_le_iff.mpr ⟨hT, hw.2.trans hTsq⟩
  rw [hsProfile_eq_paper (by norm_num) hθ]
  have ha0 : 0 ≤ a0 11883 := by unfold a0; positivity
  have ha0u := a0_upper_11883
  apply le_trans ?_ hS
  gcongr


theorem hsGroup1Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4618051055) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.679562436793 : ℝ))
    <;> norm_num

theorem hsGroup1Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4618051055 : ℝ) 0.463610211) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.741926796449 : ℝ)) (D := (1.607735442242 : ℝ))
    (Q := (0.689033424058 : ℝ)) (K := (0.832654043869 : ℝ))
    (A := (0.679562436792 : ℝ)) (T := (0.680889279546 : ℝ))
    <;> norm_num

theorem hsGroup1Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.463610211 : ℝ) 0.4654153165) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.736559308474 : ℝ)) (D := (1.604165789782 : ℝ))
    (Q := (0.688341449070 : ℝ)) (K := (0.832238504790 : ℝ))
    (A := (0.680889279545 : ℝ)) (T := (0.682213541716 : ℝ))
    <;> norm_num

theorem hsGroup1Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4654153165 : ℝ) 0.467220422) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.731233455924 : ℝ)) (D := (1.600615958460 : ℝ))
    (Q := (0.687650255608 : ℝ)) (K := (0.831823230462 : ℝ))
    (A := (0.682213541715 : ℝ)) (T := (0.683535238302 : ℝ))
    <;> norm_num

theorem hsGroup1Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.467220422 : ℝ) 0.4690255275) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.725948756223 : ℝ)) (D := (1.597085757725 : ℝ))
    (Q := (0.686959837268 : ℝ)) (K := (0.831408217431 : ℝ))
    (A := (0.683535238301 : ℝ)) (T := (0.684854384158 : ℝ))
    <;> norm_num

theorem hsGroup1Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4690255275 : ℝ) 0.470830633) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.720704734224 : ℝ)) (D := (1.593574999587 : ℝ))
    (Q := (0.686270187707 : ℝ)) (K := (0.830993462272 : ℝ))
    (A := (0.684854384157 : ℝ)) (T := (0.686170993995 : ℝ))
    <;> norm_num

theorem hsGroup1Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.470830633 : ℝ) 0.4726357385) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.715500922068 : ℝ)) (D := (1.590083498574 : ℝ))
    (Q := (0.685581300640 : ℝ)) (K := (0.830578961587 : ℝ))
    (A := (0.686170993994 : ℝ)) (T := (0.687485082384 : ℝ))
    <;> norm_num

theorem hsGroup1Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4726357385 : ℝ) 0.474440844) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  apply hs_interval_11883 hw (C := (0.710336859044 : ℝ)) (D := (1.586611071686 : ℝ))
    (Q := (0.684893169841 : ℝ)) (K := (0.830164712009 : ℝ))
    (A := (0.687485082383 : ℝ)) (T := (0.688796663755 : ℝ))
    <;> norm_num

theorem hsGroup1_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.474440844) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.161942450477 := by
  by_cases h0 : θ ≤ 0.4618051055
  · apply hsGroup1Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.463610211
  · apply hsGroup1Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4654153165
  · apply hsGroup1Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.467220422
  · apply hsGroup1Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4690255275
  · apply hsGroup1Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.470830633
  · apply hsGroup1Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.4726357385
  · apply hsGroup1Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup1Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup2Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46270765825) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680226181686 : ℝ))
    <;> norm_num

theorem hsGroup2Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.46270765825 : ℝ) 0.4654153165) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.739237817579 : ℝ)) (D := (1.605948126360 : ℝ))
    (Q := (0.688687338471 : ℝ)) (K := (0.832446241019 : ℝ))
    (A := (0.680226181685 : ℝ)) (T := (0.682213541716 : ℝ))
    <;> norm_num

theorem hsGroup2Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4654153165 : ℝ) 0.46812297475) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.731233455924 : ℝ)) (D := (1.600615958460 : ℝ))
    (Q := (0.687650255608 : ℝ)) (K := (0.831823230462 : ℝ))
    (A := (0.682213541715 : ℝ)) (T := (0.684195129149 : ℝ))
    <;> norm_num

theorem hsGroup2Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.46812297475 : ℝ) 0.470830633) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.723321689921 : ℝ)) (D := (1.595327959982 : ℝ))
    (Q := (0.686614916785 : ℝ)) (K := (0.831200807831 : ℝ))
    (A := (0.684195129148 : ℝ)) (T := (0.686170993995 : ℝ))
    <;> norm_num

theorem hsGroup2Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.470830633 : ℝ) 0.47353829125) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.715500922068 : ℝ)) (D := (1.590083498574 : ℝ))
    (Q := (0.685581300640 : ℝ)) (K := (0.830578961587 : ℝ))
    (A := (0.686170993994 : ℝ)) (T := (0.688141185550 : ℝ))
    <;> norm_num

theorem hsGroup2Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.47353829125 : ℝ) 0.4762459495) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.707769591404 : ℝ)) (D := (1.584881954517 : ℝ))
    (Q := (0.684549386110 : ℝ)) (K := (0.829957680338 : ℝ))
    (A := (0.688141185549 : ℝ)) (T := (0.690105752404 : ℝ))
    <;> norm_num

theorem hsGroup2Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4762459495 : ℝ) 0.47895360775) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.700126172464 : ℝ)) (D := (1.579722720398 : ℝ))
    (Q := (0.683519152419 : ℝ)) (K := (0.829336952827 : ℝ))
    (A := (0.690105752403 : ℝ)) (T := (0.692064742456 : ℝ))
    <;> norm_num

theorem hsGroup2Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.47895360775 : ℝ) 0.481661266) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  apply hs_interval_11883 hw (C := (0.692569174279 : ℝ)) (D := (1.574605200796 : ℝ))
    (Q := (0.682490579072 : ℝ)) (K := (0.828716767935 : ℝ))
    (A := (0.692064742455 : ℝ)) (T := (0.694018202932 : ℝ))
    <;> norm_num

theorem hsGroup2_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.481661266) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.164466752264 := by
  by_cases h0 : θ ≤ 0.46270765825
  · apply hsGroup2Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4654153165
  · apply hsGroup2Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.46812297475
  · apply hsGroup2Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.470830633
  · apply hsGroup2Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.47353829125
  · apply hsGroup2Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.4762459495
  · apply hsGroup2Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.47895360775
  · apply hsGroup2Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup2Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup3Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.463610210875) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680889279454 : ℝ))
    <;> norm_num

theorem hsGroup3Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.463610210875 : ℝ) 0.46722042175) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.736559308845 : ℝ)) (D := (1.604165790029 : ℝ))
    (Q := (0.688341449118 : ℝ)) (K := (0.832238504819 : ℝ))
    (A := (0.680889279453 : ℝ)) (T := (0.683535238119 : ℝ))
    <;> norm_num

theorem hsGroup3Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.46722042175 : ℝ) 0.470830632625) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.725948756952 : ℝ)) (D := (1.597085758212 : ℝ))
    (Q := (0.686959837364 : ℝ)) (K := (0.831408217489 : ℝ))
    (A := (0.683535238118 : ℝ)) (T := (0.686170993722 : ℝ))
    <;> norm_num

theorem hsGroup3Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.470830632625 : ℝ) 0.4744408435) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.715500923145 : ℝ)) (D := (1.590083499297 : ℝ))
    (Q := (0.685581300783 : ℝ)) (K := (0.830578961674 : ℝ))
    (A := (0.686170993721 : ℝ)) (T := (0.688796663393 : ℝ))
    <;> norm_num

theorem hsGroup3Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4744408435 : ℝ) 0.478051054375) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.705212092864 : ℝ)) (D := (1.583157539308 : ℝ))
    (Q := (0.684205789328 : ℝ)) (K := (0.829750710308 : ℝ))
    (A := (0.688796663392 : ℝ)) (T := (0.691412362036 : ℝ))
    <;> norm_num

theorem hsGroup3Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.478051054375 : ℝ) 0.48166126525) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.695078663754 : ℝ)) (D := (1.576306443166 : ℝ))
    (Q := (0.682833253862 : ℝ)) (K := (0.828923436765 : ℝ))
    (A := (0.691412362035 : ℝ)) (T := (0.694018202391 : ℝ))
    <;> norm_num

theorem hsGroup3Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.48166126525 : ℝ) 0.485271476125) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.685097141466 : ℝ)) (D := (1.569528813382 : ℝ))
    (Q := (0.681463646139 : ℝ)) (K := (0.828097114847 : ℝ))
    (A := (0.694018202390 : ℝ)) (T := (0.696614295091 : ℝ))
    <;> norm_num

theorem hsGroup3Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.485271476125 : ℝ) 0.488881687) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  apply hs_interval_11883 hw (C := (0.675264135635 : ℝ)) (D := (1.562823288792 : ℝ))
    (Q := (0.680096918775 : ℝ)) (K := (0.827271718772 : ℝ))
    (A := (0.696614295090 : ℝ)) (T := (0.699200748713 : ℝ))
    <;> norm_num

theorem hsGroup3_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.488881687) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.166975170815 := by
  by_cases h0 : θ ≤ 0.463610210875
  · apply hsGroup3Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46722042175
  · apply hsGroup3Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.470830632625
  · apply hsGroup3Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4744408435
  · apply hsGroup3Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.478051054375
  · apply hsGroup3Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.48166126525
  · apply hsGroup3Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.485271476125
  · apply hsGroup3Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup3Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup4Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.464512763625) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.681551732171 : ℝ))
    <;> norm_num

theorem hsGroup4Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.464512763625 : ℝ) 0.46902552725) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.733891208477 : ℝ)) (D := (1.602388408695 : ℝ))
    (Q := (0.687995755098 : ℝ)) (K := (0.832030834777 : ℝ))
    (A := (0.681551732170 : ℝ)) (T := (0.684854383976 : ℝ))
    <;> norm_num

theorem hsGroup4Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.46902552725 : ℝ) 0.473538290875) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.720704734947 : ℝ)) (D := (1.593575000071 : ℝ))
    (Q := (0.686270187803 : ℝ)) (K := (0.830993462330 : ℝ))
    (A := (0.684854383975 : ℝ)) (T := (0.688141185278 : ℝ))
    <;> norm_num

theorem hsGroup4Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.473538290875 : ℝ) 0.4780510545) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.707769592469 : ℝ)) (D := (1.584881955235 : ℝ))
    (Q := (0.684549386253 : ℝ)) (K := (0.829957680424 : ℝ))
    (A := (0.688141185277 : ℝ)) (T := (0.691412362126 : ℝ))
    <;> norm_num

theorem hsGroup4Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4780510545 : ℝ) 0.482563818125) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.695078663406 : ℝ)) (D := (1.576306442931 : ℝ))
    (Q := (0.682833253815 : ℝ)) (K := (0.828923436737 : ℝ))
    (A := (0.691412362125 : ℝ)) (T := (0.694668135246 : ℝ))
    <;> norm_num

theorem hsGroup4Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.482563818125 : ℝ) 0.48707658175) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.682625096370 : ℝ)) (D := (1.567845724471 : ℝ))
    (Q := (0.681121696037 : ℝ)) (K := (0.827890679993 : ℝ))
    (A := (0.694668135245 : ℝ)) (T := (0.697908720214 : ℝ))
    <;> norm_num

theorem hsGroup4Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.48707658175 : ℝ) 0.491589345375) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.670402293885 : ℝ)) (D := (1.559497149873 : ℝ))
    (Q := (0.679414620581 : ℝ)) (K := (0.826859359936 : ℝ))
    (A := (0.697908720213 : ℝ)) (T := (0.701134327626 : ℝ))
    <;> norm_num

theorem hsGroup4Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.491589345375 : ℝ) 0.496102109) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  apply hs_interval_11883 hw (C := (0.658403900732 : ℝ)) (D := (1.551258154190 : ℝ))
    (Q := (0.677711937150 : ℝ)) (K := (0.825829427288 : ℝ))
    (A := (0.701134327625 : ℝ)) (T := (0.704345163255 : ℝ))
    <;> norm_num

theorem hsGroup4_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.496102109) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.169467336900 := by
  by_cases h0 : θ ≤ 0.464512763625
  · apply hsGroup4Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46902552725
  · apply hsGroup4Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.473538290875
  · apply hsGroup4Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4780510545
  · apply hsGroup4Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.482563818125
  · apply hsGroup4Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.48707658175
  · apply hsGroup4Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.491589345375
  · apply hsGroup4Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup4Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup5Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.465415316375) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682213541624 : ℝ))
    <;> norm_num

theorem hsGroup5Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.465415316375 : ℝ) 0.47083063275) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.731233456291 : ℝ)) (D := (1.600615958705 : ℝ))
    (Q := (0.687650255656 : ℝ)) (K := (0.831823230491 : ℝ))
    (A := (0.682213541623 : ℝ)) (T := (0.686170993813 : ℝ))
    <;> norm_num

theorem hsGroup5Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.47083063275 : ℝ) 0.476245949125) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.715500922786 : ℝ)) (D := (1.590083499056 : ℝ))
    (Q := (0.685581300736 : ℝ)) (K := (0.830578961645 : ℝ))
    (A := (0.686170993812 : ℝ)) (T := (0.690105752132 : ℝ))
    <;> norm_num

theorem hsGroup5Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.476245949125 : ℝ) 0.4816612655) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.700126173516 : ℝ)) (D := (1.579722721109 : ℝ))
    (Q := (0.683519152561 : ℝ)) (K := (0.829336952913 : ℝ))
    (A := (0.690105752131 : ℝ)) (T := (0.694018202572 : ℝ))
    <;> norm_num

theorem hsGroup5Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4816612655 : ℝ) 0.487076581875) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.685097140780 : ℝ)) (D := (1.569528812915 : ℝ))
    (Q := (0.681463646044 : ℝ)) (K := (0.828097114790 : ℝ))
    (A := (0.694018202571 : ℝ)) (T := (0.697908720304 : ℝ))
    <;> norm_num

theorem hsGroup5Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.487076581875 : ℝ) 0.49249189825) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.670402293549 : ℝ)) (D := (1.559497149643 : ℝ))
    (Q := (0.679414620534 : ℝ)) (K := (0.826859359908 : ℝ))
    (A := (0.697908720303 : ℝ)) (T := (0.701777670100 : ℝ))
    <;> norm_num

theorem hsGroup5Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.49249189825 : ℝ) 0.497907214625) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.656030607967 : ℝ)) (D := (1.549623284316 : ℝ))
    (Q := (0.677371919643 : ℝ)) (K := (0.825623602943 : ℝ))
    (A := (0.701777670099 : ℝ)) (T := (0.705625406732 : ℝ))
    <;> norm_num

theorem hsGroup5Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.497907214625 : ℝ) 0.503322531) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  apply hs_interval_11883 hw (C := (0.641971539765 : ℝ)) (D := (1.539902939098 : ℝ))
    (Q := (0.675335391081 : ℝ)) (K := (0.824389760540 : ℝ))
    (A := (0.705625406731 : ℝ)) (T := (0.709452275351 : ℝ))
    <;> norm_num

theorem hsGroup5_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.503322531) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.171942889019 := by
  by_cases h0 : θ ≤ 0.465415316375
  · apply hsGroup5Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47083063275
  · apply hsGroup5Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.476245949125
  · apply hsGroup5Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4816612655
  · apply hsGroup5Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.487076581875
  · apply hsGroup5Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.49249189825
  · apply hsGroup5Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.497907214625
  · apply hsGroup5Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup5Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup6Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.466317869) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682874709592 : ℝ))
    <;> norm_num

theorem hsGroup6Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.466317869 : ℝ) 0.472635738) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.728585992568 : ℝ)) (D := (1.598848416567 : ℝ))
    (Q := (0.687304950041 : ℝ)) (K := (0.831615691556 : ℝ))
    (A := (0.682874709591 : ℝ)) (T := (0.687485082020 : ℝ))
    <;> norm_num

theorem hsGroup6Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.472635738 : ℝ) 0.478953607) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.710336860469 : ℝ)) (D := (1.586611072645 : ℝ))
    (Q := (0.684893170031 : ℝ)) (K := (0.830164712123 : ℝ))
    (A := (0.687485082019 : ℝ)) (T := (0.692064741914 : ℝ))
    <;> norm_num

theorem hsGroup6Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.478953607 : ℝ) 0.485271476) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.692569176360 : ℝ)) (D := (1.574605202207 : ℝ))
    (Q := (0.682490579357 : ℝ)) (K := (0.828716768107 : ℝ))
    (A := (0.692064741913 : ℝ)) (T := (0.696614295002 : ℝ))
    <;> norm_num

theorem hsGroup6Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.485271476 : ℝ) 0.491589345) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.675264135973 : ℝ)) (D := (1.562823289023 : ℝ))
    (Q := (0.680096918822 : ℝ)) (K := (0.827271718800 : ℝ))
    (A := (0.696614295001 : ℝ)) (T := (0.701134327359 : ℝ))
    <;> norm_num

theorem hsGroup6Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.491589345 : ℝ) 0.497907214) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.658403901720 : ℝ)) (D := (1.551258154870 : ℝ))
    (Q := (0.677711937291 : ℝ)) (K := (0.825829427373 : ℝ))
    (A := (0.701134327358 : ℝ)) (T := (0.705625406289 : ℝ))
    <;> norm_num

theorem hsGroup6Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.497907214 : ℝ) 0.504225083) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.641971541370 : ℝ)) (D := (1.539902940212 : ℝ))
    (Q := (0.675335391316 : ℝ)) (K := (0.824389760683 : ℝ))
    (A := (0.705625406288 : ℝ)) (T := (0.710088081157 : ℝ))
    <;> norm_num

theorem hsGroup6Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.504225083 : ℝ) 0.510542952) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  apply hs_interval_11883 hw (C := (0.625950971323 : ℝ)) (D := (1.528751086200 : ℝ))
    (Q := (0.672967044794 : ℝ)) (K := (0.822952589102 : ℝ))
    (A := (0.710088081156 : ℝ)) (T := (0.714522884169 : ℝ))
    <;> norm_num

theorem hsGroup6_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.510542952) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.174401474165 := by
  by_cases h0 : θ ≤ 0.466317869
  · apply hsGroup6Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.472635738
  · apply hsGroup6Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.478953607
  · apply hsGroup6Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.485271476
  · apply hsGroup6Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.491589345
  · apply hsGroup6Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.497907214
  · apply hsGroup6Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.504225083
  · apply hsGroup6Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup6Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup7Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46722042175) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.683535238119 : ℝ))
    <;> norm_num

theorem hsGroup7Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.46722042175 : ℝ) 0.4744408435) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.725948756952 : ℝ)) (D := (1.597085758212 : ℝ))
    (Q := (0.686959837364 : ℝ)) (K := (0.831408217489 : ℝ))
    (A := (0.683535238118 : ℝ)) (T := (0.688796663393 : ℝ))
    <;> norm_num

theorem hsGroup7Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4744408435 : ℝ) 0.48166126525) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.705212092864 : ℝ)) (D := (1.583157539308 : ℝ))
    (Q := (0.684205789328 : ℝ)) (K := (0.829750710308 : ℝ))
    (A := (0.688796663392 : ℝ)) (T := (0.694018202391 : ℝ))
    <;> norm_num

theorem hsGroup7Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.48166126525 : ℝ) 0.488881687) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.685097141466 : ℝ)) (D := (1.569528813382 : ℝ))
    (Q := (0.681463646139 : ℝ)) (K := (0.828097114847 : ℝ))
    (A := (0.694018202390 : ℝ)) (T := (0.699200748713 : ℝ))
    <;> norm_num

theorem hsGroup7Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.488881687 : ℝ) 0.49610210875) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.665576356044 : ℝ)) (D := (1.556188543355 : ℝ))
    (Q := (0.678733025230 : ℝ)) (K := (0.826447223160 : ℝ))
    (A := (0.699200748712 : ℝ)) (T := (0.704345163078 : ℝ))
    <;> norm_num

theorem hsGroup7Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.49610210875 : ℝ) 0.5033225305) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.646623793580 : ℝ)) (D := (1.543126254481 : ℝ))
    (Q := (0.676013557515 : ℝ)) (K := (0.824800833775 : ℝ))
    (A := (0.704345163077 : ℝ)) (T := (0.709452274999 : ℝ))
    <;> norm_num

theorem hsGroup7Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.5033225305 : ℝ) 0.51054295225) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.628214999718 : ℝ)) (D := (1.530331997975 : ℝ))
    (Q := (0.673304886680 : ℝ)) (K := (0.823157751338 : ℝ))
    (A := (0.709452274998 : ℝ)) (T := (0.714522884344 : ℝ))
    <;> norm_num

theorem hsGroup7Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.51054295225 : ℝ) 0.517763374) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  apply hs_interval_11883 hw (C := (0.610326903497 : ℝ)) (D := (1.517796317488 : ℝ))
    (Q := (0.670606668540 : ℝ)) (K := (0.821517786292 : ℝ))
    (A := (0.714522884343 : ℝ)) (T := (0.719557762797 : ℝ))
    <;> norm_num

theorem hsGroup7_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.517763374) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.176842748529 := by
  by_cases h0 : θ ≤ 0.46722042175
  · apply hsGroup7Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4744408435
  · apply hsGroup7Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.48166126525
  · apply hsGroup7Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.488881687
  · apply hsGroup7Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.49610210875
  · apply hsGroup7Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.5033225305
  · apply hsGroup7Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.51054295225
  · apply hsGroup7Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup7Cell7_11883
  exact ⟨by linarith, hw.2⟩

theorem hsGroup8Cell0_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4681229745) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.747336409998 : ℝ)) (D := (1.611325108992 : ℝ))
    (Q := (0.689726187034 : ℝ)) (K := (0.833069851183 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.684195128966 : ℝ))
    <;> norm_num

theorem hsGroup8Cell1_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4681229745 : ℝ) 0.476245949) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.723321690647 : ℝ)) (D := (1.595327960468 : ℝ))
    (Q := (0.686614916880 : ℝ)) (K := (0.831200807888 : ℝ))
    (A := (0.684195128965 : ℝ)) (T := (0.690105752041 : ℝ))
    <;> norm_num

theorem hsGroup8Cell2_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.476245949 : ℝ) 0.4843689235) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.700126173867 : ℝ)) (D := (1.579722721346 : ℝ))
    (Q := (0.683519152609 : ℝ)) (K := (0.829336952942 : ℝ))
    (A := (0.690105752040 : ℝ)) (T := (0.695966179854 : ℝ))
    <;> norm_num

theorem hsGroup8Cell3_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.4843689235 : ℝ) 0.492491898) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.677708645031 : ℝ)) (D := (1.564492983011 : ℝ))
    (Q := (0.680438333106 : ℝ)) (K := (0.827477982366 : ℝ))
    (A := (0.695966179853 : ℝ)) (T := (0.701777669922 : ℝ))
    <;> norm_num

theorem hsGroup8Cell4_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.492491898 : ℝ) 0.5006148725) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.656030608624 : ℝ)) (D := (1.549623284768 : ℝ))
    (Q := (0.677371919737 : ℝ)) (K := (0.825623603000 : ℝ))
    (A := (0.701777669921 : ℝ)) (T := (0.707541428116 : ℝ))
    <;> norm_num

theorem hsGroup8Cell5_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.5006148725 : ℝ) 0.508737847) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.635056067644 : ℝ)) (D := (1.535099044481 : ℝ))
    (Q := (0.674319395030 : ℝ)) (K := (0.823773531838 : ℝ))
    (A := (0.707541428115 : ℝ)) (T := (0.713258611585 : ℝ))
    <;> norm_num

theorem hsGroup8Cell6_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.508737847 : ℝ) 0.5168608215) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.614751324136 : ℝ)) (D := (1.520906495301 : ℝ))
    (Q := (0.671280261450 : ℝ)) (K := (0.821927495414 : ℝ))
    (A := (0.713258611584 : ℝ)) (T := (0.718930331465 : ℝ))
    <;> norm_num

theorem hsGroup8Cell7_11883 {θ : ℝ}
    (hw : θ ∈ Icc (0.5168608215 : ℝ) 0.524983796) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  apply hs_interval_11883 hw (C := (0.595084798526 : ℝ)) (D := (1.507032627889 : ℝ))
    (Q := (0.668254040262 : ℝ)) (K := (0.820085229225 : ℝ))
    (A := (0.718930331464 : ℝ)) (T := (0.724557655401 : ℝ))
    <;> norm_num

theorem hsGroup8_11883 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.524983796) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ 0.179266375202 := by
  by_cases h0 : θ ≤ 0.4681229745
  · apply hsGroup8Cell0_11883
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.476245949
  · apply hsGroup8Cell1_11883
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4843689235
  · apply hsGroup8Cell2_11883
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.492491898
  · apply hsGroup8Cell3_11883
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.5006148725
  · apply hsGroup8Cell4_11883
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.508737847
  · apply hsGroup8Cell5_11883
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.5168608215
  · apply hsGroup8Cell6_11883
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup8Cell7_11883
  exact ⟨by linarith, hw.2⟩

end BstLean.Part281.HS11883


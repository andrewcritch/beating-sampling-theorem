import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup4Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4644978935) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.681540823062 : ℝ))
    <;> norm_num

theorem hsGroup4Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.4644978935 : ℝ) 0.468995787) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.733935083103 : ℝ)) (D := (1.601914350000 : ℝ))
    (Q := (0.687902610003 : ℝ)) (K := (0.831937620689 : ℝ))
    (A := (0.681540823061 : ℝ)) (T := (0.684832670804 : ℝ))
    <;> norm_num

theorem hsGroup4Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.468995787 : ℝ) 0.4734936805) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.720790806454 : ℝ)) (D := (1.593135672905 : ℝ))
    (Q := (0.686182855524 : ℝ)) (K := (0.830903536954 : ℝ))
    (A := (0.684832670803 : ℝ)) (T := (0.688108770835 : ℝ))
    <;> norm_num

theorem hsGroup4Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.4734936805 : ℝ) 0.477991574) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.707896254602 : ℝ)) (D := (1.584476520068 : ℝ))
    (Q := (0.684467847076 : ℝ)) (K := (0.829871039948 : ℝ))
    (A := (0.688108770834 : ℝ)) (T := (0.691369347021 : ℝ))
    <;> norm_num

theorem hsGroup4Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.477991574 : ℝ) 0.4824894675) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.695244377826 : ℝ)) (D := (1.575934088902 : ℝ))
    (Q := (0.682757488936 : ℝ)) (K := (0.828840077852 : ℝ))
    (A := (0.691369347020 : ℝ)) (T := (0.694614617972 : ℝ))
    <;> norm_num

theorem hsGroup4Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.4824894675 : ℝ) 0.486987361) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.682828389285 : ℝ)) (D := (1.567505668164 : ℝ))
    (Q := (0.681051687539 : ℝ)) (K := (0.827810599887 : ℝ))
    (A := (0.694614617971 : ℝ)) (T := (0.697844797215 : ℝ))
    <;> norm_num

theorem hsGroup4Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.486987361 : ℝ) 0.4914852545) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.670641752873 : ℝ)) (D := (1.559188634153 : ℝ))
    (Q := (0.679350351405 : ℝ)) (K := (0.826782556277 : ℝ))
    (A := (0.697844797214 : ℝ)) (T := (0.701060093359 : ℝ))
    <;> norm_num

theorem hsGroup4Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.4914852545 : ℝ) 0.495983148) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  apply hs_interval hw (C := (0.658678171750 : ℝ)) (D := (1.550980447103 : ℝ))
    (Q := (0.677653391074 : ℝ)) (K := (0.825755898216 : ℝ))
    (A := (0.701060093358 : ℝ)) (T := (0.704260710249 : ℝ))
    <;> norm_num

theorem hsGroup4 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.495983148) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.169199068410 := by
  by_cases h0 : θ ≤ 0.4644978935
  · apply hsGroup4Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.468995787
  · apply hsGroup4Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4734936805
  · apply hsGroup4Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.477991574
  · apply hsGroup4Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4824894675
  · apply hsGroup4Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.486987361
  · apply hsGroup4Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.4914852545
  · apply hsGroup4Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup4Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

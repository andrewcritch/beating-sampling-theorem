import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup7Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.467196629625) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.683517834168 : ℝ))
    <;> norm_num

theorem hsGroup7Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.467196629625 : ℝ) 0.47439325925) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.726018146159 : ℝ)) (D := (1.596632640679 : ℝ))
    (Q := (0.686870182347 : ℝ)) (K := (0.831316977097 : ℝ))
    (A := (0.683517834167 : ℝ)) (T := (0.688762120946 : ℝ))
    <;> norm_num

theorem hsGroup7Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.47439325925 : ℝ) 0.481589888875) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.705346685984 : ℝ)) (D := (1.582758784055 : ℝ))
    (Q := (0.684125406429 : ℝ)) (K := (0.829664726364 : ℝ))
    (A := (0.688762120945 : ℝ)) (T := (0.693966777934 : ℝ))
    <;> norm_num

theorem hsGroup7Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.481589888875 : ℝ) 0.4887865185) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.685293032978 : ℝ)) (D := (1.569182358506 : ℝ))
    (Q := (0.681392487671 : ℝ)) (K := (0.828016379136 : ℝ))
    (A := (0.693966777933 : ℝ)) (T := (0.699132690196 : ℝ))
    <;> norm_num

theorem hsGroup7Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.4887865185 : ℝ) 0.495983148125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.665829898358 : ℝ)) (D := (1.555892437001 : ℝ))
    (Q := (0.678671047082 : ℝ)) (K := (0.826371729466 : ℝ))
    (A := (0.699132690195 : ℝ)) (T := (0.704260710338 : ℝ))
    <;> norm_num

theorem hsGroup7Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.495983148125 : ℝ) 0.50317977775) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.646931577167 : ℝ)) (D := (1.542878647532 : ℝ))
    (Q := (0.675960718988 : ℝ)) (K := (0.824730577804 : ℝ))
    (A := (0.704260710337 : ℝ)) (T := (0.709351660145 : ℝ))
    <;> norm_num

theorem hsGroup7Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.50317977775 : ℝ) 0.510376407375) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.628573835006 : ℝ)) (D := (1.530131137330 : ℝ))
    (Q := (0.673261150344 : ℝ)) (K := (0.823092730654 : ℝ))
    (A := (0.709351660144 : ℝ)) (T := (0.714406332122 : ℝ))
    <;> norm_num

theorem hsGroup7Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.510376407375 : ℝ) 0.517573037) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  apply hs_interval hw (C := (0.610733804359 : ℝ)) (D := (1.517640539858 : ℝ))
    (Q := (0.670572000086 : ℝ)) (K := (0.821458000243 : ℝ))
    (A := (0.714406332121 : ℝ)) (T := (0.719425490931 : ℝ))
    <;> norm_num

theorem hsGroup7 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.517573037) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.176542781247 := by
  by_cases h0 : θ ≤ 0.467196629625
  · apply hsGroup7Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47439325925
  · apply hsGroup7Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.481589888875
  · apply hsGroup7Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4887865185
  · apply hsGroup7Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.495983148125
  · apply hsGroup7Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.50317977775
  · apply hsGroup7Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.510376407375
  · apply hsGroup7Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup7Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

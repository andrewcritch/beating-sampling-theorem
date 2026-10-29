import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup6Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.466297050875) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682859466417 : ℝ))
    <;> norm_num

theorem hsGroup6Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.466297050875 : ℝ) 0.47259410175) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.728646943044 : ℝ)) (D := (1.598388353017 : ℝ))
    (Q := (0.687214132479 : ℝ)) (K := (0.831523793433 : ℝ))
    (A := (0.682859466416 : ℝ)) (T := (0.687454799787 : ℝ))
    <;> norm_num

theorem hsGroup6Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.47259410175 : ℝ) 0.478891152625) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.710455529382 : ℝ)) (D := (1.586198924654 : ℝ))
    (Q := (0.684810473728 : ℝ)) (K := (0.830077414924 : ℝ))
    (A := (0.687454799786 : ℝ)) (T := (0.692019618671 : ℝ))
    <;> norm_num

theorem hsGroup6Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.478891152625 : ℝ) 0.4851882035) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.692742521959 : ℝ)) (D := (1.574239369257 : ℝ))
    (Q := (0.682415967103 : ℝ)) (K := (0.828634065153 : ℝ))
    (A := (0.692019618670 : ℝ)) (T := (0.696554522992 : ℝ))
    <;> norm_num

theorem hsGroup6Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.4851882035 : ℝ) 0.491485254375) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.675489293681 : ℝ)) (D := (1.562502245920 : ℝ))
    (Q := (0.680030355835 : ℝ)) (K := (0.827193604767 : ℝ))
    (A := (0.696554522991 : ℝ)) (T := (0.701060093270 : ℝ))
    <;> norm_num

theorem hsGroup6Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.491485254375 : ℝ) 0.49778230525) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.658678172080 : ℝ)) (D := (1.550980447330 : ℝ))
    (Q := (0.677653391121 : ℝ)) (K := (0.825755898245 : ℝ))
    (A := (0.701060093269 : ℝ)) (T := (0.705536891488 : ℝ))
    <;> norm_num

theorem hsGroup6Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.49778230525 : ℝ) 0.504079356125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.642292378928 : ℝ)) (D := (1.539667180749 : ℝ))
    (Q := (0.675284831757 : ℝ)) (K := (0.824320813713 : ℝ))
    (A := (0.705536891487 : ℝ)) (T := (0.709985461912 : ℝ))
    <;> norm_num

theorem hsGroup6Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.504079356125 : ℝ) 0.510376407) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  apply hs_interval hw (C := (0.626315974385 : ℝ)) (D := (1.528555950308 : ℝ))
    (Q := (0.672924443797 : ℝ)) (K := (0.822888222771 : ℝ))
    (A := (0.709985461911 : ℝ)) (T := (0.714406331859 : ℝ))
    <;> norm_num

theorem hsGroup6 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.510376407) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.174111921985 := by
  by_cases h0 : θ ≤ 0.466297050875
  · apply hsGroup6Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.47259410175
  · apply hsGroup6Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.478891152625
  · apply hsGroup6Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4851882035
  · apply hsGroup6Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.491485254375
  · apply hsGroup6Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.49778230525
  · apply hsGroup6Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.504079356125
  · apply hsGroup6Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup6Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

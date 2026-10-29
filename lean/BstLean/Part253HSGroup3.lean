import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup3Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.463598314875) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680880543764 : ℝ))
    <;> norm_num

theorem hsGroup3Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.463598314875 : ℝ) 0.46719662975) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.736594544822 : ℝ)) (D := (1.603684681474 : ℝ))
    (Q := (0.688247138973 : ℝ)) (K := (0.832144632462 : ℝ))
    (A := (0.680880543763 : ℝ)) (T := (0.683517834259 : ℝ))
    <;> norm_num

theorem hsGroup3Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.46719662975 : ℝ) 0.470794944625) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.726018145795 : ℝ)) (D := (1.596632640436 : ℝ))
    (Q := (0.686870182299 : ℝ)) (K := (0.831316977068 : ℝ))
    (A := (0.683517834258 : ℝ)) (T := (0.686144988050 : ℝ))
    <;> norm_num

theorem hsGroup3Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.470794944625 : ℝ) 0.4743932595) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.715603418910 : ℝ)) (D := (1.589657827462 : ℝ))
    (Q := (0.685496287945 : ℝ)) (K := (0.830490350618 : ℝ))
    (A := (0.686144988049 : ℝ)) (T := (0.688762121128 : ℝ))
    <;> norm_num

theorem hsGroup3Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.4743932595 : ℝ) 0.477991574375) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.705346685277 : ℝ)) (D := (1.582758783579 : ℝ))
    (Q := (0.684125406334 : ℝ)) (K := (0.829664726306 : ℝ))
    (A := (0.688762121127 : ℝ)) (T := (0.691369347293 : ℝ))
    <;> norm_num

theorem hsGroup3Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.477991574375 : ℝ) 0.48158988925) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.695244376781 : ℝ)) (D := (1.575934088194 : ℝ))
    (Q := (0.682757488794 : ℝ)) (K := (0.828840077766 : ℝ))
    (A := (0.691369347292 : ℝ)) (T := (0.693966778204 : ℝ))
    <;> norm_num

theorem hsGroup3Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.48158988925 : ℝ) 0.485188204125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.685293031948 : ℝ)) (D := (1.569182357806 : ℝ))
    (Q := (0.681392487529 : ℝ)) (K := (0.828016379050 : ℝ))
    (A := (0.693966778203 : ℝ)) (T := (0.696554523441 : ℝ))
    <;> norm_num

theorem hsGroup3Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.485188204125 : ℝ) 0.488786519) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  apply hs_interval hw (C := (0.675489291991 : ℝ)) (D := (1.562502244766 : ℝ))
    (Q := (0.680030355598 : ℝ)) (K := (0.827193604623 : ℝ))
    (A := (0.696554523440 : ℝ)) (T := (0.699132690554 : ℝ))
    <;> norm_num

theorem hsGroup3 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.488786519) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.166717763490 := by
  by_cases h0 : θ ≤ 0.463598314875
  · apply hsGroup3Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46719662975
  · apply hsGroup3Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.470794944625
  · apply hsGroup3Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4743932595
  · apply hsGroup3Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.477991574375
  · apply hsGroup3Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.48158988925
  · apply hsGroup3Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.485188204125
  · apply hsGroup3Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup3Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

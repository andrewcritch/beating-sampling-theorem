import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup5Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46539747225) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.682200463391 : ℝ))
    <;> norm_num

theorem hsGroup5Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.46539747225 : ℝ) 0.4707949445) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.731285902099 : ℝ)) (D := (1.600148914848 : ℝ))
    (Q := (0.687558274736 : ℝ)) (K := (0.831730674469 : ℝ))
    (A := (0.682200463390 : ℝ)) (T := (0.686144987959 : ℝ))
    <;> norm_num

theorem hsGroup5Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.4707949445 : ℝ) 0.47619241675) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.715603419269 : ℝ)) (D := (1.589657827703 : ℝ))
    (Q := (0.685496287992 : ℝ)) (K := (0.830490350646 : ℝ))
    (A := (0.686144987958 : ℝ)) (T := (0.690066965410 : ℝ))
    <;> norm_num

theorem hsGroup5Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.47619241675 : ℝ) 0.481589889) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.700276447208 : ℝ)) (D := (1.579337230004 : ℝ))
    (Q := (0.683441080134 : ℝ)) (K := (0.829252281739 : ℝ))
    (A := (0.690066965409 : ℝ)) (T := (0.693966778024 : ℝ))
    <;> norm_num

theorem hsGroup5Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.481589889 : ℝ) 0.48698736125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.685293032635 : ℝ)) (D := (1.569182358273 : ℝ))
    (Q := (0.681392487623 : ℝ)) (K := (0.828016379107 : ℝ))
    (A := (0.693966778023 : ℝ)) (T := (0.697844797395 : ℝ))
    <;> norm_num

theorem hsGroup5Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.48698736125 : ℝ) 0.4923848335) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.670641752202 : ℝ)) (D := (1.559188633694 : ℝ))
    (Q := (0.679350351311 : ℝ)) (K := (0.826782556221 : ℝ))
    (A := (0.697844797394 : ℝ)) (T := (0.701701384850 : ℝ))
    <;> norm_num

theorem hsGroup5Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.4923848335 : ℝ) 0.49778230575) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.656311683449 : ℝ)) (D := (1.549351652992 : ℝ))
    (Q := (0.677314516257 : ℝ)) (K := (0.825550728573 : ℝ))
    (A := (0.701701384849 : ℝ)) (T := (0.705536891842 : ℝ))
    <;> norm_num

theorem hsGroup5Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.49778230575 : ℝ) 0.503179778) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  apply hs_interval hw (C := (0.642292377643 : ℝ)) (D := (1.539667179858 : ℝ))
    (Q := (0.675284831569 : ℝ)) (K := (0.824320813599 : ℝ))
    (A := (0.705536891841 : ℝ)) (T := (0.709351660321 : ℝ))
    <;> norm_num

theorem hsGroup5 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.503179778) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.171663904382 := by
  by_cases h0 : θ ≤ 0.46539747225
  · apply hsGroup5Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4707949445
  · apply hsGroup5Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.47619241675
  · apply hsGroup5Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.481589889
  · apply hsGroup5Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.48698736125
  · apply hsGroup5Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.4923848335
  · apply hsGroup5Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.49778230575
  · apply hsGroup5Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup5Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup2Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.462698736125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.680219623449 : ℝ))
    <;> norm_num

theorem hsGroup2Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.462698736125 : ℝ) 0.46539747225) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.739264347961 : ℝ)) (D := (1.605459933417 : ℝ))
    (Q := (0.688591862538 : ℝ)) (K := (0.832351710273 : ℝ))
    (A := (0.680219623448 : ℝ)) (T := (0.682200463391 : ℝ))
    <;> norm_num

theorem hsGroup2Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.46539747225 : ℝ) 0.468096208375) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.731285902099 : ℝ)) (D := (1.600148914848 : ℝ))
    (Q := (0.687558274736 : ℝ)) (K := (0.831730674469 : ℝ))
    (A := (0.682200463390 : ℝ)) (T := (0.684175568386 : ℝ))
    <;> norm_num

theorem hsGroup2Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.468096208375 : ℝ) 0.4707949445) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.723399453222 : ℝ)) (D := (1.594881754903 : ℝ))
    (Q := (0.686526423606 : ℝ)) (K := (0.831110225068 : ℝ))
    (A := (0.684175568385 : ℝ)) (T := (0.686144987959 : ℝ))
    <;> norm_num

theorem hsGroup2Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.4707949445 : ℝ) 0.473493680625) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.715603419269 : ℝ)) (D := (1.589657827703 : ℝ))
    (Q := (0.685496287992 : ℝ)) (K := (0.830490350646 : ℝ))
    (A := (0.686144987958 : ℝ)) (T := (0.688108770926 : ℝ))
    <;> norm_num

theorem hsGroup2Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.473493680625 : ℝ) 0.47619241675) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.707896254247 : ℝ)) (D := (1.584476519829 : ℝ))
    (Q := (0.684467847028 : ℝ)) (K := (0.829871039919 : ℝ))
    (A := (0.688108770925 : ℝ)) (T := (0.690066965410 : ℝ))
    <;> norm_num

theorem hsGroup2Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.47619241675 : ℝ) 0.478891152875) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.700276447208 : ℝ)) (D := (1.579337230004 : ℝ))
    (Q := (0.683441080134 : ℝ)) (K := (0.829252281739 : ℝ))
    (A := (0.690066965409 : ℝ)) (T := (0.692019618852 : ℝ))
    <;> norm_num

theorem hsGroup2Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.478891152875 : ℝ) 0.481589889) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  apply hs_interval hw (C := (0.692742521265 : ℝ)) (D := (1.574239368787 : ℝ))
    (Q := (0.682415967008 : ℝ)) (K := (0.828634065095 : ℝ))
    (A := (0.692019618851 : ℝ)) (T := (0.693966778024 : ℝ))
    <;> norm_num

theorem hsGroup2 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.481589889) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.164220346040 := by
  by_cases h0 : θ ≤ 0.462698736125
  · apply hsGroup2Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.46539747225
  · apply hsGroup2Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.468096208375
  · apply hsGroup2Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.4707949445
  · apply hsGroup2Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.473493680625
  · apply hsGroup2Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.47619241675
  · apply hsGroup2Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.478891152875
  · apply hsGroup2Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup2Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

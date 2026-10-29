import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup8Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.46809620825) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.684175568294 : ℝ))
    <;> norm_num

theorem hsGroup8Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.46809620825 : ℝ) 0.4761924165) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.723399453586 : ℝ)) (D := (1.594881755146 : ℝ))
    (Q := (0.686526423654 : ℝ)) (K := (0.831110225097 : ℝ))
    (A := (0.684175568293 : ℝ)) (T := (0.690066965229 : ℝ))
    <;> norm_num

theorem hsGroup8Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.4761924165 : ℝ) 0.48428862475) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.700276447910 : ℝ)) (D := (1.579337230478 : ℝ))
    (Q := (0.683441080229 : ℝ)) (K := (0.829252281797 : ℝ))
    (A := (0.690066965228 : ℝ)) (T := (0.695908488776 : ℝ))
    <;> norm_num

theorem hsGroup8Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.48428862475 : ℝ) 0.492384833) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.677926570735 : ℝ)) (D := (1.564165632500 : ℝ))
    (Q := (0.680370622365 : ℝ)) (K := (0.827399213110 : ℝ))
    (A := (0.695908488775 : ℝ)) (T := (0.701701384494 : ℝ))
    <;> norm_num

theorem hsGroup8Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.492384833 : ℝ) 0.50048104125) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.656311684761 : ℝ)) (D := (1.549351653895 : ℝ))
    (Q := (0.677314516445 : ℝ)) (K := (0.825550728687 : ℝ))
    (A := (0.701701384493 : ℝ)) (T := (0.707446846944 : ℝ))
    <;> norm_num

theorem hsGroup8Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.50048104125 : ℝ) 0.5085772495) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.635396120455 : ℝ)) (D := (1.534880854550 : ℝ))
    (Q := (0.674272249763 : ℝ)) (K := (0.823706548217 : ℝ))
    (A := (0.707446846943 : ℝ)) (T := (0.713146022565 : ℝ))
    <;> norm_num

theorem hsGroup8Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.5085772495 : ℝ) 0.51667345775) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.615146479623 : ℝ)) (D := (1.520739599291 : ℝ))
    (Q := (0.671243329320 : ℝ)) (K := (0.821866400820 : ℝ))
    (A := (0.713146022564 : ℝ)) (T := (0.718800012347 : ℝ))
    <;> norm_num

theorem hsGroup8Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.51667345775 : ℝ) 0.524769666) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  apply hs_interval hw (C := (0.595531457452 : ℝ)) (D := (1.506915001012 : ℝ))
    (Q := (0.668227280703 : ℝ)) (K := (0.820030024483 : ℝ))
    (A := (0.718800012346 : ℝ)) (T := (0.724409874312 : ℝ))
    <;> norm_num

theorem hsGroup8 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.524769666) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.178956148662 := by
  by_cases h0 : θ ≤ 0.46809620825
  · apply hsGroup8Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.4761924165
  · apply hsGroup8Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.48428862475
  · apply hsGroup8Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.492384833
  · apply hsGroup8Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.50048104125
  · apply hsGroup8Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.5085772495
  · apply hsGroup8Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.51667345775
  · apply hsGroup8Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup8Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

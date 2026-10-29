import BstLean.Part253HS

/-! Rational interval certificates for one local centre window. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem hsGroup1Cell0 {θ : ℝ}
    (hw : θ ∈ Icc (0.460000000 : ℝ) 0.4617991575) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.747336409998 : ℝ)) (D := (1.610815449278 : ℝ))
    (Q := (0.689627208469 : ℝ)) (K := (0.832973344050 : ℝ))
    (A := (0.678232998312 : ℝ)) (T := (0.679558060434 : ℝ))
    <;> norm_num

theorem hsGroup1Cell1 {θ : ℝ}
    (hw : θ ∈ Icc (0.4617991575 : ℝ) 0.463598315) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.741944552211 : ℝ)) (D := (1.607240129148 : ℝ))
    (Q := (0.688936781401 : ℝ)) (K := (0.832558854496 : ℝ))
    (A := (0.679558060433 : ℝ)) (T := (0.680880543855 : ℝ))
    <;> norm_num

theorem hsGroup1Cell2 {θ : ℝ}
    (hw : θ ∈ Icc (0.463598315 : ℝ) 0.4653974725) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.736594544452 : ℝ)) (D := (1.603684681228 : ℝ))
    (Q := (0.688247138925 : ℝ)) (K := (0.832144632433 : ℝ))
    (A := (0.680880543854 : ℝ)) (T := (0.682200463574 : ℝ))
    <;> norm_num

theorem hsGroup1Cell3 {θ : ℝ}
    (hw : θ ∈ Icc (0.4653974725 : ℝ) 0.467196630) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.731285901364 : ℝ)) (D := (1.600148914358 : ℝ))
    (Q := (0.687558274640 : ℝ)) (K := (0.831730674411 : ℝ))
    (A := (0.682200463573 : ℝ)) (T := (0.683517834442 : ℝ))
    <;> norm_num

theorem hsGroup1Cell4 {θ : ℝ}
    (hw : θ ∈ Icc (0.467196630 : ℝ) 0.4689957875) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.726018145066 : ℝ)) (D := (1.596632639949 : ℝ))
    (Q := (0.686870182204 : ℝ)) (K := (0.831316977011 : ℝ))
    (A := (0.683517834441 : ℝ)) (T := (0.684832671169 : ℝ))
    <;> norm_num

theorem hsGroup1Cell5 {θ : ℝ}
    (hw : θ ∈ Icc (0.4689957875 : ℝ) 0.470794945) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.720790805007 : ℝ)) (D := (1.593135671936 : ℝ))
    (Q := (0.686182855333 : ℝ)) (K := (0.830903536839 : ℝ))
    (A := (0.684832671168 : ℝ)) (T := (0.686144988323 : ℝ))
    <;> norm_num

theorem hsGroup1Cell6 {θ : ℝ}
    (hw : θ ∈ Icc (0.470794945 : ℝ) 0.4725941025) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.715603417833 : ℝ)) (D := (1.589657826739 : ℝ))
    (Q := (0.685496287802 : ℝ)) (K := (0.830490350532 : ℝ))
    (A := (0.686144988322 : ℝ)) (T := (0.687454800333 : ℝ))
    <;> norm_num

theorem hsGroup1Cell7 {θ : ℝ}
    (hw : θ ∈ Icc (0.4725941025 : ℝ) 0.474393260) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  apply hs_interval hw (C := (0.710455527245 : ℝ)) (D := (1.586198923217 : ℝ))
    (Q := (0.684810473443 : ℝ)) (K := (0.830077414753 : ℝ))
    (A := (0.687454800332 : ℝ)) (T := (0.688762121491 : ℝ))
    <;> norm_num

theorem hsGroup1 {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.474393260) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ 0.161707182529 := by
  by_cases h0 : θ ≤ 0.4617991575
  · apply hsGroup1Cell0
    exact ⟨by have := hw.1; linarith, h0⟩
  by_cases h1 : θ ≤ 0.463598315
  · apply hsGroup1Cell1
    exact ⟨by have := hw.1; linarith, h1⟩
  by_cases h2 : θ ≤ 0.4653974725
  · apply hsGroup1Cell2
    exact ⟨by have := hw.1; linarith, h2⟩
  by_cases h3 : θ ≤ 0.467196630
  · apply hsGroup1Cell3
    exact ⟨by have := hw.1; linarith, h3⟩
  by_cases h4 : θ ≤ 0.4689957875
  · apply hsGroup1Cell4
    exact ⟨by have := hw.1; linarith, h4⟩
  by_cases h5 : θ ≤ 0.470794945
  · apply hsGroup1Cell5
    exact ⟨by have := hw.1; linarith, h5⟩
  by_cases h6 : θ ≤ 0.4725941025
  · apply hsGroup1Cell6
    exact ⟨by have := hw.1; linarith, h6⟩
  apply hsGroup1Cell7
  exact ⟨by linarith, hw.2⟩

end BstLean.Part253

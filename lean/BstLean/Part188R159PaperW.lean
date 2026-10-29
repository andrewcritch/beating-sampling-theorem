import BstLean.Part187All
import BstLean.Part159PaperW
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R159Hat
import BstLean.Part188R159Win
import BstLean.Part188R159Frame
import BstLean.Part188R159Paper
import BstLean.Part188R159PaperF





namespace BstLean.Part188.Base159_R
open BstLean.Part159 BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **The retained World window for the centre and the scalar of the paper (every
`n ≥ 16 384`)**, IF `ConstC n` and `ConstK n`. -/
theorem theta_window_paper (hn : 16200 ≤ n) (hC : ConstC n) (hK : ConstK n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) *
        (2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1) ∧
      994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1057 / 1000 ∧
      (c ∈ Ethm D.toCentres → 465 / 1000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 528 / 1000) := by
  have hθ : c.1.1 ∈ GPap n := hc
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨-, hA1, hA2⟩ := pap_window hn hC hK hθ
  obtain ⟨t2, t1⟩ := pap_tau hn hC hK hθ
  rw [hD, hτ]
  set B := 2 / (mW n : ℝ) * normSq (bWp c.1.1) with hB
  set w0 := B * ccP n c.1.1 - 1 with hw0
  have t3 : 994 / 1000 ≤ w0 := by linarith
  have t4 : w0 ≤ 1057 / 1000 := by linarith
  have hBnn : 0 ≤ B := mul_nonneg (by positivity) (normSq_nonneg _)
  have hBpos : 0 < B := by
    rcases hBnn.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hA1; norm_num at hA1
    · exact h0
  have hnB : 0 < (n : ℝ) * B := by positivity
  refine ⟨t1, t2, t3, t4, ?_, ?_⟩
  · intro hm
    have h1 : normSq c.1.2 ≤ cUp * n * B := by
      have : normSq c.1.2 ≤ cUp * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) := hm
      rwa [hD] at this
    have hcu : cUp ≤ 1143166 / 1000000 := by
      unfold cUp
      have := sqrt45_bounds.2
      linarith
    unfold thetaIn
    rw [hτ, t2, le_div_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : normSq c.1.2 ≤ 1143166 / 1000000 * ((n : ℝ) * B) := by
      have := mul_le_mul_of_nonneg_right hcu hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t3 hnB.le]
  · intro hp
    have h1 : (1 - 2 * √(12 / (n : ℝ))) * n * B ≤ normSq c.1.2 := by
      have : (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤
          normSq c.1.2 := hp
      rwa [hD] at this
    have hcl : (945566 / 1000000 : ℝ) ≤ 1 - 2 * √(12 / (n : ℝ)) := by
      have := sqrt12n_le hn
      linarith
    unfold thetaIn
    rw [hτ, t2, div_le_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : 945566 / 1000000 * ((n : ℝ) * B) ≤ normSq c.1.2 := by
      have := mul_le_mul_of_nonneg_right hcl hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t4 hnB.le]

end BstLean.Part188.Base159_R


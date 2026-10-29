import BstLean.Part227Moment
import BstLean.Part160Comb

/-! Part 227: the retained World noise window with variable product endpoints. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part159

noncomputable def noiseLower (Alo : ℝ) : ℝ := (Alo - 1) / (cUp + (Alo - 1))
noncomputable def noiseUpper (n : ℕ) (Ahi : ℝ) : ℝ :=
  (Ahi - 1) / ((1 - 2 * √(12 / (n : ℝ))) + (Ahi - 1))

/-- An energy-ratio window transfers to a noise-fraction window. -/
theorem fraction_window {z x w l u a b : ℝ} (hz : 0 < z) (hx : 0 ≤ x)
    (hl : 0 < l) (hu : 0 < u) (ha : 0 < a) (haw : a ≤ w) (hwb : w ≤ b)
    (hxl : l * z ≤ x) (hxu : x ≤ u * z) :
    a / (u + a) ≤ z * w / (x + z * w) ∧
      z * w / (x + z * w) ≤ b / (l + b) := by
  have hw : 0 < w := ha.trans_le haw
  have hb : 0 < b := hw.trans_le hwb
  have hd : 0 < x + z * w := by positivity
  constructor
  · rw [div_le_div_iff₀ (by positivity) hd]
    have h1 := mul_le_mul_of_nonneg_left hxu ha.le
    have h2 := mul_le_mul_of_nonneg_left haw (mul_nonneg hu.le hz.le)
    nlinarith only [h1, h2]
  · rw [div_le_div_iff₀ hd (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hxl hb.le
    have h2 := mul_le_mul_of_nonneg_left hwb (mul_nonneg hl.le hz.le)
    nlinarith only [h1, h2]

theorem noise_window {n : ℕ} (hn : 4096 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c, D.tau0 c = tau0p c.1.1)
    {c : Ret n} {eB Alo Ahi : ℝ}
    (hB : c.1.1 ∈ goodB n eB) (hS : c.1.1 ∈ goodS n) (hA : c.1.1 ∈ goodAo n)
    (hL : 0 ≤ BstLean.Part140.kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(BstLean.Part140.kap1 (2 * n) - eB))
    (hk : kernelError n < BstLean.Part140.kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi)
    (hm : c ∈ Ethm D.toCentres) (hp : c ∈ Ethp D.toCentres) :
    noiseLower Alo ≤ BstLean.Part150.thetaC c.1.2 (D.tau0 c) ∧
      BstLean.Part150.thetaC c.1.2 (D.tau0 c) ≤ noiseUpper n Ahi := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hpl, hpu⟩ := product_window hn hB hS hA hL hLE hk
  have hplo := hlo.trans hpl
  have hphi := hpu.trans hhi
  obtain ⟨_, hscale⟩ := scale_identity hn hB hS hA hL hLE hk hAlo hlo
  let B : ℝ := 2 / (mW n : ℝ) * normSq (bWp c.1.1)
  let w : ℝ := B * ccP n c.1.1 - 1
  have hBn : 0 ≤ B := mul_nonneg (by positivity) (normSq_nonneg _)
  have hBp : 0 < B := by
    by_contra h
    have he : B = 0 := le_antisymm (not_lt.mp h) hBn
    change Alo ≤ B * ccP n c.1.1 at hplo
    rw [he, zero_mul] at hplo
    linarith
  have hcl : 0 < 1 - 2 * √(12 / (n : ℝ)) := by
    have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : √(12 / (n : ℝ)) < 1 / 2 := by
      rw [Real.sqrt_lt (by positivity) (by norm_num)]
      rw [div_lt_iff₀ hnpos]
      linarith
    linarith
  have hcu : 0 < cUp := by unfold cUp; positivity
  have hxl : (1 - 2 * √(12 / (n : ℝ))) * ((n : ℝ) * B) ≤ normSq c.1.2 := by
    change (1 - 2 * √(12 / (n : ℝ))) * n *
      (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤ normSq c.1.2 at hp
    rw [hD] at hp
    simpa only [mul_assoc] using hp
  have hxu : normSq c.1.2 ≤ cUp * ((n : ℝ) * B) := by
    change normSq c.1.2 ≤ cUp * n *
      (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) at hm
    rw [hD] at hm
    simpa only [mul_assoc] using hm
  have h := fraction_window (z := (n : ℝ) * B) (x := normSq c.1.2) (w := w)
    (l := 1 - 2 * √(12 / (n : ℝ))) (u := cUp) (a := Alo - 1) (b := Ahi - 1)
    (by positivity) (normSq_nonneg _) hcl hcu (by linarith)
    (by dsimp [w, B]; linarith) (by dsimp [w, B]; linarith) hxl hxu
  have he := BstLean.Part160.thetaIn_eq D c
  rw [← he]
  unfold thetaIn
  rw [hτ c, hscale]
  simpa only [noiseLower, noiseUpper, B, w, mul_assoc] using h

end BstLean.Part227
#print axioms BstLean.Part227.fraction_window
#print axioms BstLean.Part227.noise_window

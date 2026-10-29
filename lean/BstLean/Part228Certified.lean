import BstLean.Part228Cover
import BstLean.Part228NumericRoot

/-! Certified numerical latitude tails from dimension 8000. -/
namespace BstLean.Part228
open Real MeasureTheory Set
open BstLean.Part161 (muI)
open BstLean.Part157 (latitude)

theorem inverse_sqrt_certificate {n : ℕ} (hn : 8000 ≤ n) :
    Bounds (1 / √(n : ℝ)) 0 (112/10000) ∧
      (n : ℝ) * (1 / √(n : ℝ))^2 = 1 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 := sqrt_pos.mpr hn0
  have hs : (625/7 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by nlinarith)
  constructor
  · constructor
    · positivity
    · rw [div_le_iff₀ hs0]
      nlinarith
  · rw [div_pow, one_pow, sq_sqrt hn0.le]
    exact mul_one_div_cancel hn0.ne'

theorem normalized_bulk_exponents {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hθl : 46/100 ≤ θ) (hθu : θ ≤ 54/100) :
    normalizedExponent n θ (√(1-θ)-6*√(θ/n)) (-(8/√(n : ℝ))) ≤ -377/10 ∧
    normalizedExponent n θ (√(1-θ)+6*√(θ/n)) (8/√(n : ℝ)) ≤ -41 := by
  let x : ℝ := 1/√(n : ℝ)
  obtain ⟨hx, hnx⟩ := inverse_sqrt_certificate hn
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨hl, hu⟩ := scaled_cells_cover ⟨hθl, hθu⟩ hx
  obtain ⟨hblo, hord, hbhi⟩ := normalized_bulk_frontier (by omega : 4096 ≤ n) hθl hθu
  have hem : endpointAt θ x (-1) = √(1-θ)-6*√(θ/n) := by
    rw [sqrt_div hθ0.le]
    dsimp [endpointAt, x]
    ring
  have hep : endpointAt θ x 1 = √(1-θ)+6*√(θ/n) := by
    rw [sqrt_div hθ0.le]
    dsimp [endpointAt, x]
    ring
  have hdm : 1-(endpointAt θ x (-1))^2 ≠ 0 := by
    rw [hem]
    nlinarith
  have hdp : 1-(endpointAt θ x 1)^2 ≠ 0 := by
    rw [hep]
    nlinarith
  have hm := (normalizedExponent_le_scaled (by omega : 1 ≤ n) hθ0.ne' hx.1 hnx
    hl.1 hl.2.1 (endpointAt_drift hθ0 hθ1 (Or.inl rfl) hdm)).trans hl.2.2
  have hp := (normalizedExponent_le_scaled (by omega : 1 ≤ n) hθ0.ne' hx.1 hnx
    hu.1 hu.2.1 (endpointAt_drift hθ0 hθ1 (Or.inr rfl) hdp)).trans hu.2.2
  change normalizedExponent n θ (endpointAt θ x (-1)) ((-1*8)*x) ≤ _ at hm
  change normalizedExponent n θ (endpointAt θ x 1) ((1*8)*x) ≤ _ at hp
  rw [hem] at hm
  rw [hep] at hp
  have hum : ((-1*8) : ℝ)*x = -(8/√(n : ℝ)) := by dsimp [x]; ring
  have hup : ((1*8) : ℝ)*x = 8/√(n : ℝ) := by dsimp [x]; ring
  rw [hum] at hm
  rw [hup] at hp
  exact ⟨hm, hp⟩

/-- The actual transform root has this checked numerical envelope. -/
theorem normalized_bulk_root_envelope {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hθl : 46/100 ≤ θ) (hθu : θ ≤ 54/100) :
    √(2*normalizedTailMass n θ (√(1-θ)-6*√(θ/n)) (√(1-θ)+6*√(θ/n))
      (-(8/√(n : ℝ))) (8/√(n : ℝ))) ≤
    √(2*(exp (-(100 : ℝ)) + exp (-(377/10 : ℝ)) + exp (-(41 : ℝ)))) := by
  obtain ⟨hl, hu⟩ := normalized_bulk_exponents hn hθl hθu
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ0 : 0 < θ := by linarith
  have hc : (8000 : ℝ)*(46/100) ≤ n*(1-θ) :=
    mul_le_mul hnR (by linarith) (by norm_num) (by linarith)
  have ha : -(n*(1-θ)/(2*θ)) ≤ -(100 : ℝ) := by
    have h : (100 : ℝ) ≤ n*(1-θ)/(2*θ) := by
      rw [le_div_iff₀ (by positivity : 0 < 2*θ)]
      linarith
    linarith
  apply sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact add_le_add (add_le_add (exp_le_exp.mpr ha)
    (exp_le_exp.mpr (by simpa only [neg_div] using hl)))
    (exp_le_exp.mpr hu)

theorem normalized_bulk_root_lt {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hθl : 46/100 ≤ θ) (hθu : θ ≤ 54/100) :
    √(2*normalizedTailMass n θ (√(1-θ)-6*√(θ/n)) (√(1-θ)+6*√(θ/n))
      (-(8/√(n : ℝ))) (8/√(n : ℝ))) < 1/10^8 :=
  (normalized_bulk_root_envelope hn hθl hθu).trans_lt certified_exponent_root_lt

theorem normalized_latitude_tail_lt {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hθl : 46/100 ≤ θ) (hθu : θ ≤ 54/100) :
    √(2*(muI n).real {p | latitude (√(1-θ)) (√(θ/n)) p ∉
      Icc (√(1-θ)-6*√(θ/n)) (√(1-θ)+6*√(θ/n))}) < 1/10^8 :=
  (normalized_bulk_tail_explicit (by omega) hθl hθu).trans_lt
    (normalized_bulk_root_lt hn hθl hθu)

end BstLean.Part228

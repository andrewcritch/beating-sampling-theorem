import BstLean.Part290MomentBounds

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part140 BstLean.Part159
open BstLean.Part227 BstLean.Part233 BstLean.Part236

theorem window_guards {n : ℕ} (ha : 8000 ≤ n) :
    0 ≤ kap1 (2*n)-1232/10^7 ∧
    √(perturbation n) < √(kap1 (2*n)-1232/10^7) ∧
    kernelError n < kap1 (2*n) := by
  have hk := (kernel_window ha).1
  have hp := (perturbation_bounds ha).2
  have he := (kernel_error_bounds ha).2
  refine ⟨by linarith, ?_, by linarith⟩
  exact Real.sqrt_lt_sqrt (by unfold perturbation; positivity) (by linarith)

noncomputable def worldFrameCertificate {n : ℕ} (ha : 8000 ≤ n) :
    FrameCertificate n (4/100) (4/10000) (525/10000) (25/10^7) (1232/10^7) where
  r0 := worldR0 n
  k0 := worldK0 n
  k6 := worldK6 n
  ε₁ := 22287/10^6
  ε₂ := 12375/10^6
  s := worldS n
  r0_nonneg := (worldR0_bounds ha).1
  radius := by
    have hn := n_positive ha
    unfold worldR0
    rw [div_pow, mul_pow, Real.sq_sqrt hn.le]
    have he : (1 : ℝ)^2 / ((n : ℝ)^2 * n) * (n : ℝ)^3 = 1 := by
      field_simp [ne_of_gt hn]
      <;> ring
    rw [he]
  k0_nonneg := sqrt_nonneg _
  kernel := by
    unfold worldK0
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (worldR0_bounds ha).1)]
  k6_nonneg := sqrt_nonneg _
  sixth := by unfold worldK6; rw [Real.sq_sqrt (by positivity)]
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := lt_of_lt_of_le (by norm_num) (denominator_bounds ha).1
  norm_lower := (window_guards ha).1
  norm_separation := (window_guards ha).2.1
  denominator := le_refl _

theorem frameBase_eq {n : ℕ} (ha : 8000 ≤ n) :
    frameBase (worldFrameCertificate ha) (1/10^9) (1/10^12) = worldC1 n := by
  have hs : √(1/10^12 : ℝ) = 1/10^6 := by norm_num
  unfold frameBase coeffK coeffD worldFrameCertificate worldC1 worldAK worldAD
  dsimp only
  rw [hs]

theorem frame_caps {n : ℕ} (ha : 8000 ≤ n) :
    frameBase (worldFrameCertificate ha) (1/10^9) (1/10^12) ≤ 419/1000 ∧
    coeffK (worldFrameCertificate ha) (1/10^9) ≤ 1219/10^5 ∧
    coeffD (worldFrameCertificate ha) (1/10^9) ≤ 787/10^8 := by
  rw [frameBase_eq ha]
  exact ⟨(frame_bounds ha).2.trans (by norm_num),
    (coeffK_bounds ha).2.trans (by norm_num), (coeffD_bounds ha).2.trans (by norm_num)⟩

theorem product_lower {n : ℕ} (ha : 8000 ≤ n) :
    (202278/100000 : ℝ) ≤ productLower n (1232/10^7) :=
  (by norm_num : (202278/100000 : ℝ) ≤ _).trans (product_lower_bounds ha).1

theorem product_upper {n : ℕ} (ha : 8000 ≤ n) :
    productUpper n (1232/10^7) ≤ (202798/100000 : ℝ) :=
  (product_upper_bounds ha).2.trans (by norm_num)

theorem product_order {n : ℕ} (ha : 8000 ≤ n) :
    1 < productLower n (1232/10^7) ∧
    productLower n (1232/10^7) ≤ productUpper n (1232/10^7) := by
  have h1 := product_lower ha
  have h2 := (product_lower_bounds ha).2
  have h3 := (product_upper_bounds ha).1
  constructor <;> linarith

theorem displayed_noise_guards {n : ℕ} (ha : 8000 ≤ n) :
    (46/100 : ℝ) ≤ (productLower n (1232/10^7)-1)/
      (114/100+productLower n (1232/10^7)-1) ∧
    noiseUpper n (productUpper n (1232/10^7)) ≤ 54/100 := by
  have hl := product_lower ha
  have hh := product_upper ha
  have hp := (product_upper_bounds ha).1
  have hn := n_positive ha
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hs : √(12/(n : ℝ)) ≤ 4/100 := sqrt_le_iff.mpr ⟨by norm_num, by
    apply (div_le_iff₀ hn).mpr
    linarith⟩
  constructor
  · apply (le_div_iff₀ (by linarith)).mpr
    linarith
  · unfold noiseUpper
    apply (div_le_iff₀ (by linarith)).mpr
    linarith

theorem noise_caps {n : ℕ} (ha : 8000 ≤ n) :
    (472/1000 : ℝ) ≤ noiseLower (202278/100000) ∧
    noiseUpper n (202798/100000) ≤ 528/1000 :=
  ⟨(by norm_num : (472/1000 : ℝ) ≤ _).trans (noise_lower_bounds ha).1,
    (noise_upper_bounds ha).2.trans (by norm_num)⟩

theorem moment_cap {n : ℕ} (ha : 8000 ≤ n) :
    momentValue n (202278/100000) (202798/100000) (22/1000) ≤ 3164/10^11 :=
  (moment_bounds ha).2.trans (by norm_num)

theorem hidden_cap {n : ℕ} (ha : 8000 ≤ n) :
    groupedCharge n (4/100) (4/10000) (25/10^7) (1232/10^7) (805/10^9) < 1092/10^6 :=
  lt_of_le_of_lt (hidden_bounds ha).2 (by norm_num)

end BstLean.Part290

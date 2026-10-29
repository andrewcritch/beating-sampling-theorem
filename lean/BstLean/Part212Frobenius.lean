import BstLean.Part167Y
import BstLean.Part212Components

/-! The masked Frobenius moment has an order-160 supply from dimension 8000. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part151 (mask mask_nonneg mask_sq measurable_mask)
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC)
open BstLean.Part53 (unitF53)
open BstLean.Part167
variable {n m : ℕ}

theorem masked_frob_moment80 (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M)
    (h2 : 80 / M * γ < 1 / 2)
    (hnum : ((1 + phi1 (80 / M * γ) ^ (n - 1)) / 2) ^ m ≤ exp 80) :
    ∫⁻ A, ENNReal.ofReal (Qf A x ^ 80) ∂gaussMat m n γ ≤ ENNReal.ofReal (M ^ 80) := by
  have ht : 0 ≤ 80 / M := by positivity
  obtain ⟨hI, hE⟩ := Q_int (m := m) hn hx hγ ht h2
  have hpt : ∀ A : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (Qf A x ^ 80) ≤
      ENNReal.ofReal ((M / exp 1) ^ 80 * exp (80 / M * Qf A x)) := fun A =>
    ENNReal.ofReal_le_ofReal (BstLean.Part166.pow_le_exp_bound (Qf_nonneg A hx) hM 80)
  refine (lintegral_mono hpt).trans ?_
  have hInt : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => (M / exp 1) ^ 80 *
      exp (80 / M * Qf A x)) (gaussMat m n γ) := hI.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun A => by positivity),
    integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  calc (M / exp 1) ^ 80 * ∫ A, exp (80 / M * Qf A x) ∂gaussMat m n γ
      ≤ (M / exp 1) ^ 80 * exp 80 :=
        mul_le_mul_of_nonneg_left (hE.trans hnum) (by positivity)
    _ = M ^ 80 := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one]; field_simp; norm_num

/-- **The numerics of `Y`**: for `d ≥ 8`, `m ≥ 10⁵`, `N = md/2`, `τ = 80/(1.001N)`:
`((1 + φ₁(τ)^d)/2)^m ≤ e^{80}`. -/
lemma masked_frob_numeric80 {d m : ℕ} (hd : 8 ≤ d) (hm : 100000 ≤ m) :
    ((1 + phi1 (80 / (1001 / 1000 * ((m : ℝ) * d / 2))) ^ d) / 2) ^ m ≤ exp 80 := by
  have hdR : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  set τ : ℝ := 80 / (1001 / 1000 * ((m : ℝ) * d / 2)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 / 4000 := by
    rw [hτ, div_le_iff₀ (by positivity)]; nlinarith
  -- `φ₁(τ) ≤ exp(τ + 2τ²)`
  have hphi : phi1 τ ≤ exp (τ + 2 * τ ^ 2) := by
    unfold phi1
    have h0 : 0 < 1 - 2 * τ := by linarith
    have hs : 0 < √(1 - 2 * τ) := Real.sqrt_pos.mpr h0
    rw [inv_le_iff_one_le_mul₀ hs]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * τ + 4 * τ ^ 2 by positivity)
    have hsq : 1 ≤ (√(1 - 2 * τ) * exp (τ + 2 * τ ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h0.le, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (τ + 2 * τ ^ 2) = 2 * τ + 4 * τ ^ 2 := by push_cast; ring
      rw [e]
      have : (1 - 2 * τ) * (1 + (2 * τ + 4 * τ ^ 2) + (2 * τ + 4 * τ ^ 2) ^ 2 / 2) ≥ 1 := by
        nlinarith [mul_pos hτ0 hτ0, mul_pos (mul_pos hτ0 hτ0) hτ0,
          mul_pos (mul_pos (mul_pos hτ0 hτ0) hτ0) hτ0]
      nlinarith
    have hpos : 0 ≤ √(1 - 2 * τ) * exp (τ + 2 * τ ^ 2) := by positivity
    nlinarith [hsq, hpos]
  set Y : ℝ := d * (τ + 2 * τ ^ 2) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hphiY : phi1 τ ^ d ≤ exp Y := by
    calc phi1 τ ^ d ≤ exp (τ + 2 * τ ^ 2) ^ d :=
          pow_le_pow_left₀ (by unfold phi1; positivity) hphi d
      _ = exp Y := by rw [← Real.exp_nat_mul]
  have hcosh : (1 + exp Y) / 2 ≤ exp (Y / 2 + Y ^ 2 / 8) := by
    have hc := Real.cosh_le_exp_half_sq (Y / 2)
    rw [Real.cosh_eq] at hc
    have e1 : (1 + exp Y) / 2 = exp (Y / 2) * ((exp (Y / 2) + exp (-(Y / 2))) / 2) := by
      rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero]; ring
    rw [e1, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (hc.trans (le_of_eq (by ring_nf))) (exp_pos _).le
  have hbase : (1 + phi1 τ ^ d) / 2 ≤ exp (Y / 2 + Y ^ 2 / 8) := by
    linarith
  calc ((1 + phi1 τ ^ d) / 2) ^ m ≤ exp (Y / 2 + Y ^ 2 / 8) ^ m :=
        pow_le_pow_left₀ (by have : 0 ≤ phi1 τ ^ d := by unfold phi1; positivity
                             positivity) hbase m
    _ = exp (m * (Y / 2 + Y ^ 2 / 8)) := by rw [← Real.exp_nat_mul]
    _ ≤ exp 80 := by
        apply exp_le_exp.mpr
        have hK : (m : ℝ) * d * τ = 160000 / 1001 := by
          rw [hτ]; field_simp; norm_num
        have e : (m : ℝ) * (Y / 2 + Y ^ 2 / 8) =
            (m * d * τ) * (1 + 2 * τ) / 2 + (m * d * τ) ^ 2 * (1 + 2 * τ) ^ 2 / (8 * m) := by
          rw [hY]; field_simp
        rw [e, hK]
        have h1 : (160000 / 1001 : ℝ) * (1 + 2 * τ) / 2 ≤ 80000 / 1001 * (1 + 2 / 4000) := by
          nlinarith
        have h2 : (160000 / 1001 : ℝ) ^ 2 * (1 + 2 * τ) ^ 2 / (8 * m) ≤
            (160000 / 1001) ^ 2 * (1 + 2 / 4000) ^ 2 / (8 * 100000) := by
          apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
        have h3 : (80000 / 1001 : ℝ) * (1 + 2 / 4000) + (160000 / 1001) ^ 2 * (1 + 2 / 4000) ^ 2 /
            (8 * 100000) ≤ 80 := by norm_num
        linarith

noncomputable def frobEnvelopeSquared160 (n : ℕ) : ℝ :=
  2 / (n : ℝ) * (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2))

lemma frobEnvelope_pos160 (hn : 2 ≤ n) : 0 < frobEnvelopeSquared160 n := by
  unfold frobEnvelopeSquared160
  have h1 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have h3 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  positivity

/-- **The masked Frobenius moment is proved**: `frobMoment160 ≤ frobEnvelopeSquared160^{80}` for every `n ≥ 80 000`. -/
theorem frobMoment_bound160 (hn : 8000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    frobMoment160 c τ a v ≤ ENNReal.ofReal (frobEnvelopeSquared160 n ^ 80) := by
  have hn1 : 1 ≤ n := by omega
  have hc := window_c_ne hn1 hw
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn1 hc hv
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  set cc := √(1 - s ^ 2)
  have hsc : s ^ 2 + cc ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  have hc' : (rc c).1.2 ≠ 0 := hc
  have hx : xLat (rc c) s (unitF53 v) = s • uHat (rc c) + cc • dirW (rc c) (unitF53 v) :=
    BstLean.Part161.xLat_eq hn1 hc' s (unitF53 v)
  have hx1 : normSq (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) = 1 := by
    rw [normSq_two, hu, hw1, huw]; linarith
  unfold frobMoment160
  rw [← hsdef, hx]
  have hpt : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
        (D1A1 A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)))ᵀ) ^ 80) ≤
      ENNReal.ofReal (Qf A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) ^ 80) := fun A₁ =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (frobSq_nonneg _)
      (frob_le_Q hu hw1 huw hsc A₁) 80)
  refine (lintegral_mono hpt).trans ?_
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hM := frobEnvelope_pos160 (n := n) (by omega)
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; simp
  have hτ : 80 / frobEnvelopeSquared160 n * (2 / (n : ℝ)) =
      80 / (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2)) := by
    unfold frobEnvelopeSquared160; field_simp
  refine masked_frob_moment80 hn1 hx1 hγ hM ?_ ?_
  · rw [hτ, hmA, hd, div_lt_iff₀ (by nlinarith)]
    nlinarith
  · rw [hτ]
    exact masked_frob_numeric80 (d := n - 1) (m := mA n) (by omega) (by unfold mA; nlinarith)

end BstLean.Part212

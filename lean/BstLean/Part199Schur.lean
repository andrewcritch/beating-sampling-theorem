import BstLean.Part199Geometry
import BstLean.Part199Moments

/-! Part 199: core, shell and outside covariance reductions.
The core and wide weight bounds remain distinct. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (Xi4)
open BstLean.Part182

theorem Dq_le_two_weights {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {Ω₀ Ω₁ : Set (Fin n → ℝ)}
    (h01 : Ω₁ ⊆ Ω₀) (h0 : MeasurableSet Ω₀) (h1 : MeasurableSet Ω₁)
    {lam₁ lam₀ : ℝ} (hl₁ : 0 ≤ lam₁) (hl₀ : 0 ≤ lam₀)
    (C : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hC : MeasurableSet C)
    (hCs : ∀ a b, (a, b) ∈ C → (b, a) ∈ C)
    (G₁ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₁ : MeasurableSet G₁)
    (hGs₁ : ∀ a b, (a, b) ∈ G₁ → (b, a) ∈ G₁)
    (hpair₁ : ∀ a b, (a, b) ∈ G₁ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern C ((n : ℝ) * lam₁) ((n : ℝ) * lam₀) a b)
    (G₀ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₀ : MeasurableSet G₀)
    (hGs₀ : ∀ a b, (a, b) ∈ G₀ → (b, a) ∈ G₀)
    (hpair₀ : ∀ a b, (a, b) ∈ G₀ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      (n : ℝ) * lam₀)
    {Ew W₁ W₀ Pp Ps : ℝ}
    (hEw : ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ Ew)
    (hW₁0 : 0 ≤ W₁) (hW₀0 : 0 ≤ W₀)
    (hW₁ : ∀ ξ ∈ Ω₁, wN c τ ξ ≤ W₁) (hW₀ : ∀ ξ ∈ Ω₀, wN c τ ξ ≤ W₀)
    (hPp : ∀ ξ, (stdGauss (Fin n)).real {ξ' | ξ' ∈ Ω₁ ∧ (ξ, ξ') ∉ C} ≤ Pp)
    (hPs : (stdGauss (Fin n)).real (Ω₀ \ Ω₁) ≤ Ps) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      (2 / (mA n : ℝ) * ((n : ℝ) * lam₁ * Ew + (n : ℝ) * lam₀ * W₁ * Pp +
        (n : ℝ) * lam₀ * W₀ * Ps) + Xi4 A₁ A₂ c τ *
        (√(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁))) +
         √(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
           (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)))) +
         √((stdGauss (Fin n)).real Ω₀ᶜ))) * normSq v := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnl₁ : 0 ≤ (n : ℝ) * lam₁ := mul_nonneg (Nat.cast_nonneg _) hl₁
  have hnl₀ : 0 ≤ (n : ℝ) * lam₀ := mul_nonneg (Nat.cast_nonneg _) hl₀
  have hwi := integrable_wN (by omega) c hτ
  have hw0 := wN_nonneg c τ
  have hrow₁ : ∀ ξ, ∫ ξ', G₁.indicator (Function.uncurry (kern C ((n : ℝ) * lam₁)
      ((n : ℝ) * lam₀))) (ξ, ξ') * Ω₁.indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤
      (n : ℝ) * lam₁ * Ew + (n : ℝ) * lam₀ * W₁ * Pp := by
    intro ξ
    refine (row_bound (stdGauss (Fin n)) hC hG₁ hnl₁ hnl₀ (Ω₁.indicator (wN c τ))
      ((measurable_wN c τ).indicator h1) (fun ξ => Set.indicator_nonneg (fun _ _ => hw0 _) ξ)
      (hwi.indicator h1) h1 (fun ξ hξ => Set.indicator_of_notMem hξ _)
      (W := W₁) (fun ξ hξ => by rw [Set.indicator_of_mem hξ]; exact hW₁ ξ hξ) ξ).trans ?_
    have hi : ∫ ξ', Ω₁.indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤ Ew := by
      refine le_trans ?_ hEw
      exact integral_mono (hwi.indicator h1) hwi
        (fun ξ => Set.indicator_le_self' (fun _ _ => hw0 _) ξ)
    exact add_le_add (mul_le_mul_of_nonneg_left hi hnl₁)
      (mul_le_mul_of_nonneg_left (hPp ξ) (mul_nonneg hnl₀ hW₁0))
  have hrow₀ : ∀ ξ, ∫ ξ', G₀.indicator (Function.uncurry (kern ∅ 0 ((n : ℝ) * lam₀)))
      (ξ, ξ') * (Ω₀ \ Ω₁).indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤
      (n : ℝ) * lam₀ * W₀ * Ps := by
    intro ξ
    refine (row_bound (stdGauss (Fin n)) MeasurableSet.empty hG₀ le_rfl hnl₀
      ((Ω₀ \ Ω₁).indicator (wN c τ)) ((measurable_wN c τ).indicator (h0.diff h1))
      (fun ξ => Set.indicator_nonneg (fun _ _ => hw0 _) ξ) (hwi.indicator (h0.diff h1))
      (h0.diff h1) (fun ξ hξ => Set.indicator_of_notMem hξ _) (W := W₀)
      (fun ξ hξ => by rw [Set.indicator_of_mem hξ]; exact hW₀ ξ hξ.1) ξ).trans ?_
    have he : {ξ' | ξ' ∈ Ω₀ \ Ω₁ ∧ (ξ, ξ') ∉
        (∅ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} = Ω₀ \ Ω₁ := by ext ξ'; simp
    rw [he, zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_left hPs (mul_nonneg hnl₀ hW₀0)
  have h := Dq_le_twolevel A₁ A₂ c hn hτ h01 h0 h1
    (kern C ((n : ℝ) * lam₁) ((n : ℝ) * lam₀)) (measurable_kern hC _ _)
    (kern_nonneg C hnl₁ hnl₀) (kern_symm hCs _ _) (kern_le C hnl₁ hnl₀)
    G₁ hG₁ hGs₁ hpair₁ hrow₁
    (kern ∅ 0 ((n : ℝ) * lam₀)) (measurable_kern MeasurableSet.empty _ _)
    (kern_nonneg ∅ le_rfl hnl₀) (kern_symm (fun _ _ h => h) _ _) (kern_le ∅ le_rfl hnl₀)
    G₀ hG₀ hGs₀ (fun a b hab => by
      rw [kern_of_notMem (Set.notMem_empty _)]; exact hpair₀ a b hab) hrow₀ v
  exact h.trans (le_of_eq (by ring))

/-- Scalar normalization for the actual width mA=n^2. -/
theorem schur_scalar {n : ℕ} (hn : 0 < n)
    {Q lam₁ lam₀ E W₁ W₀ Pp Ps M θ F V : ℝ}
    (hQ : Q ≤
      (2 / (mA n : ℝ) * ((n : ℝ) * lam₁ * (E * θ / n) +
        (n : ℝ) * lam₀ * (W₁ * θ / n) * Pp +
        (n : ℝ) * lam₀ * (W₀ * θ / n) * Ps) + M * (2 / (n : ℝ)) / n * F) * V) :
    Q ≤ (θ * (lam₁ * E + lam₀ * W₁ * Pp + lam₀ * W₀ * Ps) + M * F) *
      (2 / (n : ℝ)) / n * V := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hQ
  convert hQ using 1 <;> field_simp <;> ring

/-- A scalar covariance bound transfers to the existing network interface. -/
theorem cov_of_scalar {n : ℕ} (hn : 6 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) {K N : ℝ} (hK : K ≤ N)
    (h : ∀ v, Dq c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) v ≤
      K * (2 / (n : ℝ)) / n * normSq v) : COV_at D c N := by
  refine cov_at_of_Dq hn D c hτ fun v => (h v).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 0 ≤ (2 / (n : ℝ)) / n * normSq v := by
    have := normSq_nonneg v
    positivity
  simpa only [mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hK hscale

end BstLean.Part199

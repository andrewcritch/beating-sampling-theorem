import BstLean.Part199Moments
import BstLean.Part199Events

/-! Part 199: variable-order moment supplies and retained-data charges. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4 jS)

/-- A checked concentration formula supplies the inverse-radius mean. -/
theorem Ew_of_radius_scalar {n p : ℕ} (hp : 1 ≤ p) (hn : 4 * p + 1 < n)
    (c : Fin n → ℝ) {τ ε B : ℝ} (hτ : 0 < τ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hB : 0 < B)
    (hscalar : (τ ^ 2 / ((1 - ε) ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2))) ^ p +
      √(exp (-(ε ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2))) *
        (((n : ℝ) - 1 - 4 * p)⁻¹) ^ p ≤ B ^ p) :
    ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ B := by
  have h := Wq_le_of_Wp (by omega) hp (by omega : 2 * p + 1 < n) c hτ hB
    ((WqN_le hn c hτ hε0 hε1).trans hscalar)
  simpa only [WqN, pow_one, wN] using h

/-- One actual moment event and one radius moment bound supply Xi4. -/
theorem Xi4_on_MomentEvent {n p : ℕ} (hp : 2 ≤ p) (hn : 2 * p + 1 < n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ M E : ℝ} (hτ : 0 < τ) (hM : 0 < M) (hE : 0 < E) (hθ : 0 < thetaC c τ)
    (hW : WqN p c τ ≤ (E * thetaC c τ / n) ^ p)
    (hX : ((c, τ), (A₁, A₂)) ∈ MomentEvent n p M) :
    Xi4 A₁ A₂ c τ ≤ (M * E * thetaC c τ) * (2 / (n : ℝ)) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hXp0 : XqN p A₁ A₂ c τ ≤ (M * n) ^ p * WqN p c τ := hX
  have hXp : XqN p A₁ A₂ c τ ≤ (M * E * thetaC c τ) ^ p := by
    refine hXp0.trans ((mul_le_mul_of_nonneg_left hW (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]
    congr 1
    field_simp
  exact Xi4_le_of_Xp hp hn A₁ A₂ c hτ (by positivity) hXp

theorem MomentEvent_ret_charge {n p P : ℕ} (hp : 1 ≤ p) (hP : 1 ≤ P)
    (hn : 2 * p + 1 < n) (D : Design n) (hτ : TauWorld D)
    {M η : ℝ} (hM : 0 < M) (hη : 0 ≤ η) :
    (retDist D.toCentres).real (agentEv D (MomentEvent n p M))ᶜ ≤
      (jS n (p * P) η ^ 2 / M) ^ (p * P) := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ (measurableSet_MomentEvent n p M) (by positivity)
    (fun c τ hτ => MomentEvent_charge hp hP hn c hτ hM hη)

end BstLean.Part199

import BstLean.Part205Conditional
import BstLean.Part205Taylor
import BstLean.Part201Windows

/-! The actual conditional centre ratio and its Taylor domain from dimension 4096. -/
namespace BstLean.Part205
open MeasureTheory Real
open BstLean.Part130 BstLean.Part137 BstLean.Part141

lemma firstQ_rows {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) : firstQ M₁ = rowS M₁ / (2 * (N : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < 2 / (m : ℝ) := by positivity
  apply mul_left_cancel₀ hv.ne'
  calc
    2 / (m : ℝ) * firstQ M₁ = GamS M₁ := by
      unfold GamS alphaU firstQ
      rw [integral_const_mul]
    _ = rowS M₁ / ((m : ℝ) * N) := GamS_rowS hN hm M₁
    _ = 2 / (m : ℝ) * (rowS M₁ / (2 * (N : ℝ))) := by field_simp <;> ring

/-- The ratio is deterministic once the sphere dimension is fixed. -/
theorem world_ratio {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (hQ : 0 < firstQ M₁) :
    normSq (h1bar M₁) / firstQ M₁ = 2 * (N : ℝ) * cN N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : rowS M₁ = firstQ M₁ * (2 * (N : ℝ)) :=
    (div_eq_iff (by positivity)).mp (firstQ_rows hN hm M₁).symm
  rw [normSq_h1bar hN, hS]
  field_simp [hQ.ne']
  <;> ring

theorem world_ratio_window {n m : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin (2 * n)) ℝ) (hQ : 0 < firstQ M₁) :
    317 / 1000 ≤ normSq (h1bar M₁) / firstQ M₁ ∧
    normSq (h1bar M₁) / firstQ M₁ < 31835 / 100000 := by
  rw [world_ratio (by omega) hm M₁ hQ]
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hc]
  rw [show (2 : ℝ) * (2 * (n : ℝ)) = 4 * (n : ℝ) by ring]
  exact BstLean.Part201.rN_even_window hn

/-- The global Taylor theorem applies to the actual World ratio throughout the frontier. -/
theorem world_global_taylor {n m : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin (2 * n)) ℝ) (hQ : 0 < firstQ M₁)
    {y : ℝ} (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ remainderK (normSq (h1bar M₁) / firstQ M₁) y ∧
    remainderK (normSq (h1bar M₁) / firstQ M₁) y ≤
      endpointK (normSq (h1bar M₁) / firstQ M₁) *
        (y - normSq (h1bar M₁) / firstQ M₁) ^ 2 := by
  obtain ⟨h1, h2⟩ := world_ratio_window hn hm M₁ hQ
  exact global_taylor (by linarith) (by linarith) hy0 hy1

end BstLean.Part205

#print axioms BstLean.Part205.world_ratio
#print axioms BstLean.Part205.world_ratio_window
#print axioms BstLean.Part205.world_global_taylor

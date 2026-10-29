import BstLean.Part263Energy
import BstLean.Part253Exp

/-! Exact coverage and the energy envelope for the low band. No dimension table. -/
namespace BstLean.BlueprintLow
open Real Set

def LowBand (n : ℕ) : Prop := n ∈ Icc 8000 11882

noncomputable def agentEnergyCap : ℝ := 707768 / 1000000
noncomputable def agentDirectionCap : ℝ := 109292 / 1000000
noncomputable def agentEnergyMomentCap : ℝ := 21008487 / 1000000
noncomputable def agentParallelCap : ℝ := 53854 / 1000000
noncomputable def agentLatitudeCap : ℝ := 3042 / 1000
noncomputable def weightedFrameCap : ℝ := 1553718 / 1000000

def frameDimLower (i : Fin 6) : ℕ :=
  match i.val with
  | 0 => 8000 | 1 => 8250 | 2 => 8500 | 3 => 9000 | 4 => 10000 | _ => 11000
def frameDimUpper (i : Fin 6) : ℕ :=
  match i.val with
  | 0 => 8250 | 1 => 8500 | 2 => 9000 | 3 => 10000 | 4 => 11000 | _ => 11882

theorem frame_dimension_cover {n : ℕ} (hn : LowBand n) :
    ∃ i : Fin 6, n ∈ Icc (frameDimLower i) (frameDimUpper i) := by
  obtain ⟨hl, hu⟩ := hn
  by_cases h0 : n ≤ 8250
  · exact ⟨0, hl, h0⟩
  by_cases h1 : n ≤ 8500
  · exact ⟨1, by constructor <;> norm_num [frameDimLower, frameDimUpper] <;> omega⟩
  by_cases h2 : n ≤ 9000
  · exact ⟨2, by constructor <;> norm_num [frameDimLower, frameDimUpper] <;> omega⟩
  by_cases h3 : n ≤ 10000
  · exact ⟨3, by constructor <;> norm_num [frameDimLower, frameDimUpper] <;> omega⟩
  by_cases h4 : n ≤ 11000
  · exact ⟨4, by constructor <;> norm_num [frameDimLower, frameDimUpper] <;> omega⟩
  · exact ⟨5, by constructor <;> norm_num [frameDimLower, frameDimUpper] <;> omega⟩

noncomputable def frameNoiseLower (j : Fin 160) : ℝ := 46 / 100 + j.val / 2000
noncomputable def frameNoiseUpper (j : Fin 160) : ℝ := 46 / 100 + (j.val + 1) / 2000

lemma unit_interval_cover (k : ℕ) {x : ℝ} (hx : x ∈ Icc 0 ((k + 1 : ℕ) : ℝ)) :
    ∃ i : Fin (k + 1), (i.val : ℝ) ≤ x ∧ x ≤ i.val + 1 := by
  induction k generalizing x with
  | zero => exact ⟨0, by simpa using hx.1, by simpa using hx.2⟩
  | succ k ih =>
    by_cases h : x ≤ (k + 1 : ℕ)
    · obtain ⟨i, hi⟩ := ih ⟨hx.1, h⟩
      exact ⟨⟨i.val, by omega⟩, hi⟩
    · refine ⟨⟨k + 1, by omega⟩, le_of_lt (lt_of_not_ge h), ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using hx.2

theorem frame_noise_cover {θ : ℝ} (hθ : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    ∃ j : Fin 160, θ ∈ Icc (frameNoiseLower j) (frameNoiseUpper j) := by
  obtain ⟨j, hj⟩ := unit_interval_cover 159
    (x := (θ - 46 / 100) * 2000) (by constructor <;> norm_num <;> linarith [hθ.1, hθ.2])
  refine ⟨j, ?_⟩
  dsimp [frameNoiseLower, frameNoiseUpper]
  constructor <;> linarith [hj.1, hj.2]

theorem frame_rectangle_cover {n : ℕ} (hn : LowBand n) {θ : ℝ}
    (hθ : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    ∃ i : Fin 6, ∃ j : Fin 160,
      n ∈ Icc (frameDimLower i) (frameDimUpper i) ∧
      θ ∈ Icc (frameNoiseLower j) (frameNoiseUpper j) := by
  obtain ⟨i, hi⟩ := frame_dimension_cover hn
  obtain ⟨j, hj⟩ := frame_noise_cover hθ
  exact ⟨i, j, hi, hj⟩

theorem frame_denominators {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    1 < n ∧ 0 < 1 - 6 * θ / (n : ℝ) ∧ 0 < 1 - 4 * θ / (n : ℝ) := by
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by omega, ?_, ?_⟩
  · have h : 6 * θ / (n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith [hθ.2])
    linarith
  · have h : 4 * θ / (n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith [hθ.2])
    linarith

theorem weighted_orders : (16 : ℝ) * (45 / 4) / 15 = 12 ∧
    1 < (45 / 4 : ℝ) ∧ 1 - (45 / 4 : ℝ)⁻¹ = 41 / 45 ∧
    (2 : ℝ) / (45 / 4) = 8 / 45 := by norm_num

/-- The paper's tight order-32 energy cap, uniformly for every n ≥ 8000. -/
theorem energyMomentBand {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ) * BstLean.Part222.energyAllowance n < agentEnergyMomentCap := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  let c : ℝ := (54477338763354130 / 10 ^ 16) * (14142135623730951 / 10 ^ 16)
  let r : ℝ := 13627217491968550 / 10 ^ 16
  let b : ℝ := c + 5 / (2 * (n : ℝ))
  let b0 : ℝ := c + 5 / (2 * 8000)
  have hb : b ≤ b0 := by dsimp [b, b0]; gcongr
  have hb0 : 0 ≤ b := by dsimp [b, c]; positivity
  have he : (n : ℝ) * BstLean.Part263.energyBound n = r * (2 * b + b ^ 2 / n) := by
    dsimp [BstLean.Part263.energyBound, BstLean.Part263.layerBound, r, b, c]
    field_simp
  calc
    (n : ℝ) * BstLean.Part222.energyAllowance n ≤
        (n : ℝ) * BstLean.Part263.energyBound n :=
      mul_le_mul_of_nonneg_left (BstLean.Part263.energy_allowance_bound (by omega)) hn0.le
    _ = r * (2 * b + b ^ 2 / n) := he
    _ ≤ r * (2 * b0 + b0 ^ 2 / 8000) := by gcongr
    _ < agentEnergyMomentCap := by norm_num [r, b0, c, agentEnergyMomentCap]

theorem energyAllowanceBand {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ agentEnergyMomentCap / n := by
  rw [le_div_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)]
  simpa only [mul_comm] using (energyMomentBand hn).le

theorem weightedFrameCap_lt : weightedFrameCap < (156 / 100 : ℝ) := by
  norm_num [weightedFrameCap]

end BstLean.BlueprintLow
